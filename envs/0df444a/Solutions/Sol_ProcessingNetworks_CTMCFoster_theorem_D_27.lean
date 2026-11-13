-- Prove2me | solution 1 for ProcessingNetworks.CTMCFoster.theorem_D_27
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T06:58:09.271187+00:00
-- url     : https://prove2.me/submissions/ac0ab5ed-c292-4c6a-9fb5-757f67ea3c7c

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_CTMCFoster_jumpPMF
import Definitions.Def_ProcessingNetworks_CTMCFoster_DriftConditionAt

set_option autoImplicit false

namespace CTF61

open ProcessingNetworks.Stability
open scoped ENNReal

variable {S : Type*}

/-- `h` is a finite supersolution for the expected (continuous) time to enter `C`. -/
def GoodSet (G : S → PMF S) (w : S → ℝ≥0∞) (C : Set S) : Prop :=
  ∃ h : S → ℝ≥0∞, (∀ i, h i ≠ ⊤) ∧
    ∀ i, w i + ∑' k, Cᶜ.indicator (fun k => G i k * h k) k ≤ h i

lemma good_mono {G : S → PMF S} {w : S → ℝ≥0∞} {C D : Set S} (hCD : C ⊆ D)
    (hC : GoodSet G w C) : GoodSet G w D := by
  obtain ⟨h, hfin, hh⟩ := hC
  refine ⟨h, hfin, fun i => le_trans (add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)) (hh i)⟩
  exact Set.indicator_le_indicator_of_subset (Set.compl_subset_compl.mpr hCD)
    (fun _ => zero_le) k

lemma good_step {G : S → PMF S} {w : S → ℝ≥0∞} {C : Set S} {s t : S}
    (hC : GoodSet G w C) (hs : s ∈ C) (hst : 0 < G s t) :
    GoodSet G w (insert t (C \ {s})) := by
  classical
  obtain ⟨h, hfin, hh⟩ := hC
  have hp0 : G s t ≠ 0 := hst.ne'
  have hpT : G s t ≠ ⊤ := PMF.apply_ne_top _ _
  set K : ℝ≥0∞ := h s / G s t with hK
  have hKfin : K ≠ ⊤ := ENNReal.div_ne_top (hfin s) hp0
  have hKp : K * G s t = h s := ENNReal.div_mul_cancel hp0 hpT
  set h' : S → ℝ≥0∞ := fun k => if k = s then K else h k + K with hh'
  set C' : Set S := insert t (C \ {s}) with hC'
  have htC' : t ∈ C' := Set.mem_insert _ _
  refine ⟨h', fun k => ?_, fun i => ?_⟩
  · simp only [hh']
    split_ifs
    · exact hKfin
    · exact ENNReal.add_ne_top.mpr ⟨hfin k, hKfin⟩
  have hterm : ∀ k, C'ᶜ.indicator (fun k => G i k * h' k) k ≤
      Cᶜ.indicator (fun k => G i k * h k) k + C'ᶜ.indicator (fun k => G i k) k * K := by
    intro k
    by_cases hk : k ∈ C'
    · simp [hk]
    · by_cases hks : k = s
      · rw [hks] at hk ⊢
        simp [hk, hs, hh']
      · have hkC : k ∉ C := fun hkC => hk (Set.mem_insert_of_mem _ ⟨hkC, hks⟩)
        simp [hk, hkC, hks, hh', mul_add]
  have hsum : ∑' k, C'ᶜ.indicator (fun k => G i k * h' k) k ≤
      ∑' k, Cᶜ.indicator (fun k => G i k * h k) k +
        (∑' k, C'ᶜ.indicator (fun k => G i k) k) * K := by
    calc _ ≤ ∑' k, (Cᶜ.indicator (fun k => G i k * h k) k +
            C'ᶜ.indicator (fun k => G i k) k * K) := ENNReal.tsum_le_tsum hterm
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  set B := ∑' k, C'ᶜ.indicator (fun k => G i k) k with hB
  have hB1 : B ≤ 1 := by
    calc B ≤ ∑' k, G i k := ENNReal.tsum_le_tsum fun k => Set.indicator_le_self _ _ k
      _ = 1 := (G i).tsum_coe
  have hbase : w i + ∑' k, C'ᶜ.indicator (fun k => G i k * h' k) k ≤ h i + B * K := by
    calc _ ≤ w i + (∑' k, Cᶜ.indicator (fun k => G i k * h k) k + B * K) :=
          add_le_add le_rfl hsum
      _ = (w i + ∑' k, Cᶜ.indicator (fun k => G i k * h k) k) + B * K := by rw [add_assoc]
      _ ≤ h i + B * K := add_le_add (hh i) le_rfl
  by_cases his : i = s
  · have hh's : h' i = K := by simp [hh', his]
    rw [hh's]
    have hBs : B + G i t ≤ 1 := by
      calc B + G i t = ∑' k, (C'ᶜ.indicator (fun k => G i k) k +
              (if k = t then G i t else 0)) := by
              rw [ENNReal.tsum_add, tsum_ite_eq]
        _ ≤ ∑' k, G i k := ENNReal.tsum_le_tsum fun k => by
              by_cases hkt : k = t
              · rw [hkt]; simp [htC']
              · simp only [hkt, if_false, add_zero]; exact Set.indicator_le_self _ _ k
        _ = 1 := (G i).tsum_coe
    rw [his] at hBs
    calc _ ≤ h i + B * K := hbase
      _ = K * (G s t + B) := by rw [his, ← hKp]; ring
      _ ≤ K * 1 := by gcongr; rw [add_comm]; exact hBs
      _ = K := mul_one K
  · have hh'i : h' i = h i + K := by simp [hh', his]
    rw [hh'i]
    calc _ ≤ h i + B * K := hbase
      _ ≤ h i + 1 * K := add_le_add le_rfl (by gcongr)
      _ = h i + K := by rw [one_mul]

lemma good_path (G : S → PMF S) (w : S → ℝ≥0∞) : ∀ n : ℕ, ∀ (C : Set S) (s t : S),
    GoodSet G w C → s ∈ C → 0 < stepIter G n s t → GoodSet G w (insert t (C \ {s})) := by
  intro n
  induction n with
  | zero =>
    intro C s t hC hs hst
    have hts : t = s := by
      by_contra hne
      have : stepIter G 0 s t = 0 := by
        show (PMF.pure s) t = 0
        simp [PMF.pure_apply, hne]
      exact hst.ne' this
    rw [hts]
    refine good_mono ?_ hC
    intro k hk
    by_cases hks : k = s
    · rw [hks]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨hk, hks⟩
  | succ n ih =>
    intro C s t hC hs hst
    obtain ⟨u, hu⟩ : ∃ u, 0 < G s u * stepIter G n u t := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : stepIter G (n+1) s t = 0 := by
        show ((G s).bind (stepIter G n)) t = 0
        rw [PMF.bind_apply]
        exact ENNReal.tsum_eq_zero.mpr fun u => le_antisymm (hcon u) (zero_le)
      exact hst.ne' this
    have hGu : 0 < G s u := pos_iff_ne_zero.mpr (left_ne_zero_of_mul hu.ne')
    have hPu : 0 < stepIter G n u t := pos_iff_ne_zero.mpr (right_ne_zero_of_mul hu.ne')
    have h1 := good_step hC hs hGu
    have h2 := ih _ u t h1 (Set.mem_insert _ _) hPu
    refine good_mono ?_ h2
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff] at hk ⊢
    tauto

lemma good_single (G : S → PMF S) (w : S → ℝ≥0∞) (hirr : Irreducible G) (x : S) :
    ∀ F : Finset S, GoodSet G w (insert x (F : Set S)) → GoodSet G w {x} := by
  classical
  intro F
  refine Finset.induction_on F ?_ ?_
  · intro h
    refine good_mono ?_ h
    intro k hk
    simpa using hk
  · intro a F haF ih h
    by_cases hax : a = x
    · apply ih
      refine good_mono ?_ h
      intro k hk
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hk ⊢
      rw [hax] at hk
      tauto
    · obtain ⟨n, hn⟩ := hirr a x
      have h2 := good_path G w n _ a x h (by simp) hn
      apply ih
      refine good_mono ?_ h2
      intro k hk
      simp only [Finset.coe_insert, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff,
        Finset.mem_coe] at hk ⊢
      tauto

lemma taboo_succ_sum (G : S → PMF S) (x : S) (n : ℕ) (f : S → ℝ≥0∞) :
    ∑' y, tabooProb G x (n+1) y * f y =
      ∑' z, tabooProb G x n z * ∑' k, ({x}ᶜ : Set S).indicator (fun k => G z k * f k) k := by
  classical
  have e : ∀ y, tabooProb G x (n+1) y * f y =
      ∑' z, tabooProb G x n z * ({x}ᶜ : Set S).indicator (fun k => G z k * f k) y := by
    intro y
    by_cases hy : y = x
    · rw [hy]; simp [tabooProb]
    · simp only [tabooProb, hy, if_false]
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun z => ?_
      rw [Set.indicator_of_mem (by simpa using hy), mul_assoc]
  rw [tsum_congr e, ENNReal.tsum_comm]
  exact tsum_congr fun z => ENNReal.tsum_mul_left

lemma posrec_of_good (G : S → PMF S) (rate : S → ℝ) (x : S) {K : ℝ≥0∞} (hKt : K ≠ ⊤)
    (hK : ∀ y, 1 ≤ K * ENNReal.ofReal (rate y)⁻¹)
    (hg : GoodSet G (fun y => ENNReal.ofReal (rate y)⁻¹) {x}) :
    Recurrent G x ∧ meanReturnTime G rate x < ⊤ := by
  classical
  obtain ⟨h, hfin, hh⟩ := hg
  set a : ℕ → ℝ≥0∞ := fun n => ∑' y, tabooProb G x n y * h y with ha
  set m : ℕ → ℝ≥0∞ := fun n => ∑' y, tabooProb G x n y * ENNReal.ofReal (rate y)⁻¹ with hm
  have hstep : ∀ n, m n + a (n+1) ≤ a n := by
    intro n
    simp only [hm, ha]
    rw [taboo_succ_sum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun y => ?_
    rw [← mul_add]
    gcongr
    exact hh y
  have h0 : a 0 = h x := by
    simp only [ha]
    rw [tsum_eq_single x (fun y hy => by simp [tabooProb, hy])]
    simp [tabooProb]
  have hpart : ∀ N, (∑ n ∈ Finset.range N, m n) + a N ≤ h x := by
    intro N
    induction N with
    | zero => simp [h0]
    | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc]
      exact le_trans (add_le_add le_rfl (hstep N)) ih
  have hmsum : ∑' n, m n ≤ h x :=
    ENNReal.tsum_le_of_sum_range_le fun N => le_trans le_self_add (hpart N)
  have hmt : meanReturnTime G rate x < ⊤ :=
    lt_of_le_of_lt hmsum (lt_top_iff_ne_top.mpr (hfin x))
  refine ⟨?_, hmt⟩
  set s : ℕ → ℝ≥0∞ := fun n => ∑' y, tabooProb G x n y with hs
  have hrow : ∀ z, ∑' k, ({x}ᶜ : Set S).indicator (fun k => G z k) k + G z x = 1 := by
    intro z
    have e : ∀ k, ({x}ᶜ : Set S).indicator (fun k => G z k) k +
        (if k = x then G z x else 0) = G z k := by
      intro k
      by_cases hk : k = x
      · rw [hk]; simp
      · simp [hk]
    calc _ = ∑' k, (({x}ᶜ : Set S).indicator (fun k => G z k) k +
            (if k = x then G z x else 0)) := by
            rw [ENNReal.tsum_add, tsum_ite_eq]
      _ = ∑' k, G z k := tsum_congr e
      _ = 1 := (G z).tsum_coe
  have hsf : ∀ n, s (n+1) + firstReturnProb G x n = s n := by
    intro n
    have := taboo_succ_sum G x n (fun _ => 1)
    simp only [mul_one] at this
    simp only [hs, firstReturnProb]
    rw [this, ← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [← mul_add, hrow z, mul_one]
  have hpart2 : ∀ N, (∑ n ∈ Finset.range N, firstReturnProb G x n) + s N = 1 := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, hs]
      rw [tsum_eq_single x (fun y hy => by simp [tabooProb, hy])]
      simp [tabooProb]
    | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc, add_comm (firstReturnProb G x N), hsf N, ih]
  have hsK : ∀ n, s n ≤ K * m n := by
    intro n
    simp only [hs, hm]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    calc tabooProb G x n y = tabooProb G x n y * 1 := (mul_one _).symm
      _ ≤ tabooProb G x n y * (K * ENNReal.ofReal (rate y)⁻¹) := by gcongr; exact hK y
      _ = K * (tabooProb G x n y * ENNReal.ofReal (rate y)⁻¹) := by ring
  have hsfin : ∑' n, s n ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsK)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hKt (ne_top_of_le_ne_top (hfin x) hmsum)
  have hs0 : Filter.Tendsto s Filter.atTop (nhds 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsfin
  show ∑' n, firstReturnProb G x n = 1
  apply le_antisymm
  · refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rw [← hpart2 N]
    exact le_self_add
  · have ht : Filter.Tendsto (fun N => ∑' n, firstReturnProb G x n + s N) Filter.atTop
        (nhds (∑' n, firstReturnProb G x n + 0)) := tendsto_const_nhds.add hs0
    rw [add_zero] at ht
    refine ge_of_tendsto' ht fun N => ?_
    rw [← hpart2 N]
    exact add_le_add (ENNReal.sum_le_tsum _) le_rfl

lemma nu_inv (G : S → PMF S) (x : S) (hrec : Recurrent G x) (y : S) :
    ∑' z, (∑' n, tabooProb G x n z) * G z y = ∑' n, tabooProb G x n y := by
  have hswap : ∑' z, (∑' n, tabooProb G x n z) * G z y =
      ∑' n, ∑' z, tabooProb G x n z * G z y := by
    simp_rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_comm
  rw [hswap]
  by_cases hy : y = x
  · rw [hy]
    have h1 : ∑' n, tabooProb G x n x = 1 := by
      rw [tsum_eq_single 0 (fun n hn => ?_)]
      · simp [tabooProb]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp [tabooProb]
    rw [h1]
    exact hrec
  · have hs : ∀ n, ∑' z, tabooProb G x n z * G z y = tabooProb G x (n+1) y := fun n => by
      simp [tabooProb, hy]
    simp_rw [hs]
    refine Nat.succ_injective.tsum_eq (f := fun n => tabooProb G x n y) ?_
    intro n hn
    rw [Function.mem_support] at hn
    cases n with
    | zero => exact (hn (by simp [tabooProb, hy])).elim
    | succ k => exact ⟨k, rfl⟩

lemma unique_stat (G : S → PMF S) (rate : S → ℝ) (hr : ∀ i, 0 < rate i) (hirr : Irreducible G)
    (x : S) (hrec : Recurrent G x) (hm : meanReturnTime G rate x < ⊤) :
    HasUniqueStationaryDistribution G rate := by
  classical
  set ν : S → ℝ≥0∞ := fun y => ∑' n, tabooProb G x n y with hν
  have hνx : ν x = 1 := by
    show ∑' n, tabooProb G x n x = 1
    rw [tsum_eq_single 0 (fun n hn => ?_)]
    · simp [tabooProb]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [tabooProb]
  have hinv : ∀ y, ∑' z, ν z * G z y = ν y := fun y => nu_inv G x hrec y
  set w : S → ℝ≥0∞ := fun y => ENNReal.ofReal (rate y)⁻¹ with hw
  have hwr : ∀ z, w z * ENNReal.ofReal (rate z) = 1 := by
    intro z
    simp only [hw]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hr z).le), inv_mul_cancel₀ (hr z).ne',
      ENNReal.ofReal_one]
  set M := meanReturnTime G rate x with hM
  have hMeq : ∑' y, ν y * w y = M := by
    simp only [hν, hw, hM, meanReturnTime]
    simp_rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_comm
  have hM0 : M ≠ 0 := by
    intro h0
    have h1 : ν x * w x ≤ M := hMeq ▸ ENNReal.le_tsum x
    rw [h0, hνx, one_mul] at h1
    have hwx : 0 < w x := by
      simp only [hw]
      exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (hr x))
    exact absurd (le_antisymm h1 (zero_le)) hwx.ne'
  have hMt : M ≠ ⊤ := hm.ne
  let π0 : PMF S := ⟨fun y => ν y * w y * M⁻¹, by
    rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_mul_right, hMeq, ENNReal.mul_inv_cancel hM0 hMt]⟩
  have hπ0 : ∀ y, π0 y = ν y * w y * M⁻¹ := fun y => rfl
  refine ⟨π0, ?_, ?_⟩
  · intro y
    have e : ∀ z, π0 z * ENNReal.ofReal (rate z) = ν z * M⁻¹ := by
      intro z
      rw [hπ0]
      calc ν z * w z * M⁻¹ * ENNReal.ofReal (rate z)
          = ν z * (w z * ENNReal.ofReal (rate z)) * M⁻¹ := by ring
        _ = ν z * M⁻¹ := by rw [hwr, mul_one]
    simp_rw [e]
    rw [← hinv y, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun z => by ring
  · intro π' hπ'
    set ν' : S → ℝ≥0∞ := fun z => π' z * ENNReal.ofReal (rate z) with hν'
    have hν'fin : ∀ z, ν' z ≠ ⊤ := fun z =>
      ENNReal.mul_ne_top (PMF.apply_ne_top π' z) ENNReal.ofReal_ne_top
    have hinv' : ∀ y, ∑' z, ν' z * G z y = ν' y := fun y => hπ' y
    have hlow : ∀ N y, ν' x * ∑ n ∈ Finset.range N, tabooProb G x n y ≤ ν' y := by
      intro N
      induction N with
      | zero => intro y; simp
      | succ N ih =>
        intro y
        by_cases hy : y = x
        · rw [hy, Finset.sum_range_succ', Finset.sum_eq_zero (fun n _ => by simp [tabooProb])]
          simp [tabooProb]
        · rw [Finset.sum_range_succ']
          have h0 : tabooProb G x 0 y = 0 := by simp [tabooProb, hy]
          have hs : ∀ n, tabooProb G x (n+1) y = ∑' z, tabooProb G x n z * G z y := fun n => by
            simp [tabooProb, hy]
          rw [h0, add_zero]
          simp_rw [hs]
          calc ν' x * ∑ n ∈ Finset.range N, ∑' z, tabooProb G x n z * G z y
              = ∑' z, (ν' x * ∑ n ∈ Finset.range N, tabooProb G x n z) * G z y := by
                rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
                  ← ENNReal.tsum_mul_left]
                refine tsum_congr fun z => ?_
                simp only [hν', Finset.mul_sum, Finset.sum_mul]
                exact Finset.sum_congr rfl fun n _ => by ring
            _ ≤ ∑' z, ν' z * G z y := ENNReal.tsum_le_tsum fun z => by gcongr; exact ih z
            _ = ν' y := hinv' y
    have hge : ∀ y, ν' x * ν y ≤ ν' y := by
      intro y
      show ν' x * ∑' n, tabooProb G x n y ≤ ν' y
      rw [ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
      exact iSup_le fun N => hlow N y
    set μ : S → ℝ≥0∞ := fun y => ν' y - ν' x * ν y with hμ
    have hdec : ∀ y, ν' y = ν' x * ν y + μ y := fun y => (add_tsub_cancel_of_le (hge y)).symm
    have hμinv : ∀ y, ∑' z, μ z * G z y = μ y := by
      intro y
      have e1 : ∑' z, ν' z * G z y = ν' x * ν y + ∑' z, μ z * G z y := by
        calc ∑' z, ν' z * G z y = ∑' z, (ν' x * (ν z * G z y) + μ z * G z y) := by
              refine tsum_congr fun z => ?_
              conv_lhs => rw [hdec z]
              ring
          _ = ν' x * ν y + ∑' z, μ z * G z y := by
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hinv y]
      have hfin : ν' x * ν y ≠ ⊤ := ne_top_of_le_ne_top (hν'fin y) (hge y)
      have h3 := (hinv' y).symm.trans e1
      rw [hdec y] at h3
      exact ((ENNReal.add_right_inj hfin).mp h3).symm
    have hμx : μ x = 0 := by
      show ν' x - ν' x * ν x = 0
      rw [hνx, mul_one, tsub_self]
    have hprop : ∀ n, ∑' z, μ z * stepIter G n z x = μ x := by
      intro n
      induction n with
      | zero =>
        rw [tsum_eq_single x (fun z hz => by
          show μ z * (PMF.pure z) x = 0
          simp [PMF.pure_apply, Ne.symm hz])]
        show μ x * (PMF.pure x) x = μ x
        simp
      | succ n ih =>
        calc ∑' z, μ z * stepIter G (n+1) z x
            = ∑' z, ∑' u, μ z * G z u * stepIter G n u x := by
              refine tsum_congr fun z => ?_
              show μ z * ((G z).bind (stepIter G n)) x = _
              rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
              exact tsum_congr fun u => by ring
          _ = ∑' u, ∑' z, μ z * G z u * stepIter G n u x := ENNReal.tsum_comm
          _ = ∑' u, μ u * stepIter G n u x := by
              refine tsum_congr fun u => ?_
              rw [ENNReal.tsum_mul_right, hμinv u]
          _ = μ x := ih
    have hμ0 : ∀ y, μ y = 0 := by
      intro y
      obtain ⟨n, hn⟩ := hirr y x
      have h1 : μ y * stepIter G n y x ≤ μ x := by
        calc μ y * stepIter G n y x ≤ ∑' z, μ z * stepIter G n z x := ENNReal.le_tsum y
          _ = μ x := hprop n
      rw [hμx] at h1
      have h2 : μ y * stepIter G n y x = 0 := le_antisymm h1 (zero_le)
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hn.ne'
    have hν'eq : ∀ y, ν' y = ν' x * ν y := fun y => by rw [hdec y, hμ0 y, add_zero]
    have hπ'y : ∀ y, π' y = ν' x * (ν y * w y) := by
      intro y
      calc π' y = π' y * ENNReal.ofReal (rate y) * w y := by
            rw [mul_assoc, mul_comm (ENNReal.ofReal _), hwr, mul_one]
        _ = ν' y * w y := rfl
        _ = ν' x * (ν y * w y) := by rw [hν'eq y, mul_assoc]
    have hsum1 : ν' x * M = 1 := by
      rw [← hMeq, ← ENNReal.tsum_mul_left, ← π'.tsum_coe]
      exact (tsum_congr hπ'y).symm
    have hν'x : ν' x = M⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hsum1
    ext y
    rw [hπ'y y, hπ0 y, hν'x, mul_comm]

open MatrixAnalytic.ProductForm ProcessingNetworks.CTMCFoster in
lemma drift_good {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (C : Set S)
    (V : S → ℝ) (hV : ∀ i, 0 ≤ V i) (hdrift : ∀ i, DriftConditionAt Λ V b c C i) :
    GoodSet (jumpPMF hΛ) (fun y => ENNReal.ofReal (holdRate Λ y)⁻¹) C := by
  have hr : ∀ i, 0 < holdRate Λ i := fun i => neg_pos.mpr (hΛ.2.1 i)
  refine ⟨fun k => ENNReal.ofReal (V k / c) +
      C.indicator (fun k => ENNReal.ofReal (b / c * (holdRate Λ k)⁻¹)) k, fun k => ?_, fun i => ?_⟩
  · refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
    by_cases hk : k ∈ C <;> simp [hk]
  have hlam := hr i
  have hGi : ∀ k, jumpPMF hΛ i k = ENNReal.ofReal (jumpP Λ i k) := fun k => rfl
  have hJ0 : ∀ k, 0 ≤ jumpP Λ i k := by
    intro k
    unfold jumpP
    split_ifs with h
    · exact le_rfl
    · exact div_nonneg (hΛ.1 i k (Ne.symm h)) hlam.le
  have hfun : (fun k => jumpP Λ i k * (V k / c)) =
      fun k => (Λ i k * V k + (if k = i then holdRate Λ i * V i else 0)) / (holdRate Λ i * c) := by
    funext k
    unfold jumpP
    by_cases hk : k = i
    · rw [if_pos hk, if_pos hk, hk]
      unfold holdRate
      ring
    · rw [if_neg hk, if_neg hk, add_zero, div_mul_div_comm]
  have hHS : HasSum (fun k => jumpP Λ i k * (V k / c))
      ((∑' k, Λ i k * V k + holdRate Λ i * V i) / (holdRate Λ i * c)) := by
    rw [hfun]
    exact ((hdrift i).1.hasSum.add (hasSum_ite_eq i (holdRate Λ i * V i))).div_const _
  have hnn : ∀ k, 0 ≤ jumpP Λ i k * (V k / c) := fun k =>
    mul_nonneg (hJ0 k) (div_nonneg (hV k) hc.le)
  set T := (∑' k, Λ i k * V k + holdRate Λ i * V i) / (holdRate Λ i * c) with hT
  have hT0 : 0 ≤ T := hHS.nonneg hnn
  have hsumE : ∑' k, jumpPMF hΛ i k * ENNReal.ofReal (V k / c) = ENNReal.ofReal T := by
    rw [← hHS.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hHS.summable]
    refine tsum_congr fun k => ?_
    rw [hGi, ENNReal.ofReal_mul (hJ0 k)]
  have hD := (hdrift i).2
  set A := ∑' k, Λ i k * V k with hA
  have hmain : (holdRate Λ i)⁻¹ + T ≤
      V i / c + C.indicator (fun k => b / c * (holdRate Λ k)⁻¹) i := by
    by_cases hi : i ∈ C
    · rw [Set.indicator_of_mem hi] at hD ⊢
      rw [← sub_nonneg]
      have e : V i / c + b / c * (holdRate Λ i)⁻¹ - ((holdRate Λ i)⁻¹ + T) =
          (b - c - A) / (holdRate Λ i * c) := by
        rw [hT]
        field_simp
        ring
      rw [e]
      exact div_nonneg (by linarith) (by positivity)
    · have hz : C.indicator (fun _ => b) i = 0 := by simp [hi]
      have hz' : C.indicator (fun k => b / c * (holdRate Λ k)⁻¹) i = 0 := by simp [hi]
      rw [hz] at hD
      rw [hz', ← sub_nonneg]
      have e : V i / c + 0 - ((holdRate Λ i)⁻¹ + T) = (-c - A) / (holdRate Λ i * c) := by
        rw [hT]
        field_simp
        ring
      rw [e]
      exact div_nonneg (by linarith) (by positivity)
  calc ENNReal.ofReal (holdRate Λ i)⁻¹ + ∑' k, Cᶜ.indicator (fun k => jumpPMF hΛ i k *
        (ENNReal.ofReal (V k / c) +
          C.indicator (fun k => ENNReal.ofReal (b / c * (holdRate Λ k)⁻¹)) k)) k
      ≤ ENNReal.ofReal (holdRate Λ i)⁻¹ + ∑' k, jumpPMF hΛ i k * ENNReal.ofReal (V k / c) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        by_cases hk : k ∈ C
        · simp [hk]
        · simp [hk]
    _ = ENNReal.ofReal ((holdRate Λ i)⁻¹ + T) := by
        rw [hsumE, ENNReal.ofReal_add (inv_nonneg.mpr hlam.le) hT0]
    _ ≤ ENNReal.ofReal (V i / c + C.indicator (fun k => b / c * (holdRate Λ k)⁻¹) i) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (V i / c) +
          C.indicator (fun k => ENNReal.ofReal (b / c * (holdRate Λ k)⁻¹)) i := by
        by_cases hi : i ∈ C
        · simp only [Set.indicator_of_mem hi]
          exact ENNReal.ofReal_add (div_nonneg (hV i) hc.le) (by positivity)
        · simp [hi]

end CTF61

open ProcessingNetworks ProcessingNetworks.CTMCFoster MatrixAnalytic.ProductForm in
theorem solution {S : Type*} [Countable S] [Nonempty S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (hirr : Stability.Irreducible (jumpPMF hΛ))
    (hbdd : BddAbove (Set.range (holdRate Λ)))
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (C : Set S) (hC : C.Finite)
    (V : S → ℝ) (hV : ∀ i, 0 ≤ V i) (hdrift : ∀ i, DriftConditionAt Λ V b c C i) :
    Stability.PositiveRecurrent (jumpPMF hΛ) (holdRate Λ) ∧
      Stability.HasUniqueStationaryDistribution (jumpPMF hΛ) (holdRate Λ) := by
  classical
  have hr : ∀ i, 0 < holdRate Λ i := fun i => neg_pos.mpr (hΛ.2.1 i)
  obtain ⟨L, hL⟩ := hbdd
  have hLpos : 0 < L :=
    lt_of_lt_of_le (hr (Classical.arbitrary S)) (hL (Set.mem_range_self _))
  have hK : ∀ y, 1 ≤ ENNReal.ofReal L * ENNReal.ofReal (holdRate Λ y)⁻¹ := by
    intro y
    rw [← ENNReal.ofReal_mul hLpos.le, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv, one_le_div (hr y)]
    exact hL (Set.mem_range_self y)
  have hgC := CTF61.drift_good hΛ b c hb hc C V hV hdrift
  have hsingle : ∀ x, CTF61.GoodSet (jumpPMF hΛ) (fun y => ENNReal.ofReal (holdRate Λ y)⁻¹) {x} := by
    intro x
    obtain ⟨F, hF⟩ := hC.exists_finset_coe
    refine CTF61.good_single _ _ hirr x F (CTF61.good_mono ?_ hgC)
    rw [hF]
    exact Set.subset_insert _ _
  have hpr : ∀ x, Stability.Recurrent (jumpPMF hΛ) x ∧
      Stability.meanReturnTime (jumpPMF hΛ) (holdRate Λ) x < ⊤ :=
    fun x => CTF61.posrec_of_good _ _ x ENNReal.ofReal_ne_top hK (hsingle x)
  exact ⟨hpr, CTF61.unique_stat _ _ hr hirr (Classical.arbitrary S) (hpr _).1 (hpr _).2⟩
