-- Prove2me | solution 1 for RedundancyStab.IID.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T16:08:16.094814+00:00
-- url     : https://prove2.me/submissions/c20402ca-157c-4c45-8ccf-337239261736

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_RedundancyStab_IID_ROSChain

open scoped ENNReal
open Filter Topology
open ProcessingNetworks.Stability

namespace TF50

variable {X : Type*} (jump : X → PMF X)

open Classical in
/-- killed one-step weights toward target `x` -/
noncomputable def cc (x y z : X) : ℝ≥0∞ := if z = x then 0 else jump y z

open Classical in
lemma c_split (x y : X) : jump y x + ∑' z, cc jump x y z = 1 := by
  have h : ∀ z, jump y z = (if z = x then jump y x else 0) + cc jump x y z := by
    intro z; unfold cc; split_ifs with hz
    · subst hz; simp
    · simp
  rw [← PMF.tsum_coe (jump y)]
  conv_rhs => rw [show (fun z => jump y z) =
    fun z => (if z = x then jump y x else 0) + cc jump x y z from funext h]
  rw [ENNReal.tsum_add, tsum_ite_eq]

/-- Lyapunov (supersolution) witness for target `x` -/
def Good (x : X) : Prop :=
  ∃ h : X → ℝ≥0∞, (∀ y, h y ≠ ⊤) ∧ ∀ y, 1 + ∑' z, cc jump x y z * h z ≤ h y

open Classical in
lemma taboo_succ (x : X) (n : ℕ) (y : X) :
    tabooProb jump x (n + 1) y = ∑' z, tabooProb jump x n z * cc jump x z y := by
  rw [tabooProb]
  unfold cc
  split_ifs with hy
  · simp
  · rfl

/-- surviving mass -/
noncomputable def mass (x : X) (n : ℕ) : ℝ≥0∞ := ∑' y, tabooProb jump x n y

lemma mass_succ_add (x : X) (n : ℕ) :
    mass jump x (n + 1) + firstReturnProb jump x n = mass jump x n := by
  unfold mass firstReturnProb
  simp_rw [taboo_succ]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_add]
  congr 1; funext z
  rw [← mul_add, add_comm, c_split, mul_one]

open Classical in
lemma mass_zero (x : X) : mass jump x 0 = 1 := by
  unfold mass
  simp only [tabooProb]
  rw [tsum_ite_eq]

lemma taboo_zero_mul (x : X) (h : X → ℝ≥0∞) :
    ∑' y, tabooProb jump x 0 y * h y = h x := by
  classical
  have : ∀ y, tabooProb jump x 0 y * h y = if y = x then h x else 0 := by
    intro y; simp only [tabooProb]; split_ifs with hy
    · subst hy; simp
    · simp
  simp_rw [this]; rw [tsum_ite_eq]

lemma tele (x : X) (h : X → ℝ≥0∞) (hsup : ∀ y, 1 + ∑' z, cc jump x y z * h z ≤ h y) :
    ∀ N, ∑ n ∈ Finset.range N, mass jump x n +
      ∑' y, tabooProb jump x N y * h y ≤ h x := by
  have step : ∀ n, mass jump x n + ∑' y, tabooProb jump x (n + 1) y * h y ≤
      ∑' y, tabooProb jump x n y * h y := by
    intro n
    unfold mass
    simp_rw [taboo_succ, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    rw [← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum; intro z
    calc tabooProb jump x n z + tabooProb jump x n z * ∑' y, cc jump x z y * h y
        = tabooProb jump x n z * (1 + ∑' y, cc jump x z y * h y) := by ring
      _ ≤ tabooProb jump x n z * h z := by gcongr; exact hsup z
  intro N
  induction N with
  | zero => simp [taboo_zero_mul]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc]
    calc _ ≤ ∑ n ∈ Finset.range N, mass jump x n + ∑' y, tabooProb jump x N y * h y := by
          gcongr; exact step N
      _ ≤ h x := ih

lemma mass_tsum_le (x : X) (h : X → ℝ≥0∞) (hsup : ∀ y, 1 + ∑' z, cc jump x y z * h z ≤ h y) :
    ∑' n, mass jump x n ≤ h x :=
  ENNReal.tsum_le_of_sum_range_le (fun N => le_trans le_self_add (tele jump x h hsup N))

lemma frp_partial (x : X) : ∀ N, ∑ n ∈ Finset.range N, firstReturnProb jump x n +
    mass jump x N = 1 := by
  intro N
  induction N with
  | zero => simp [mass_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, add_comm (firstReturnProb jump x N), mass_succ_add, ih]

lemma posrec_of_good (rate : X → ℝ) (r0 : ℝ) (hr0 : 0 < r0) (hr : ∀ y, r0 ≤ rate y)
    (x : X) (hg : Good jump x) : Recurrent jump x ∧ meanReturnTime jump rate x < ⊤ := by
  obtain ⟨h, hfin, hsup⟩ := hg
  have hm : ∑' n, mass jump x n ≠ ⊤ := ne_top_of_le_ne_top (hfin x) (mass_tsum_le jump x h hsup)
  constructor
  · unfold Recurrent
    have hle : ∑' n, firstReturnProb jump x n ≤ 1 :=
      ENNReal.tsum_le_of_sum_range_le (fun N => by
        rw [← frp_partial jump x N]; exact le_self_add)
    refine le_antisymm hle ?_
    have ht : Tendsto (fun N => mass jump x N) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hm
    have ht2 : Tendsto (fun N => 1 - mass jump x N) atTop (𝓝 (1 - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds ht (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at ht2
    refine le_of_tendsto' ht2 (fun N => ?_)
    calc 1 - mass jump x N = ∑ n ∈ Finset.range N, firstReturnProb jump x n := by
          rw [← frp_partial jump x N]
          exact ENNReal.add_sub_cancel_right (ne_top_of_le_ne_top ENNReal.one_ne_top
            (by rw [← frp_partial jump x N]; exact le_add_self))
      _ ≤ _ := ENNReal.sum_le_tsum _
  · unfold meanReturnTime
    have hb : ∀ n y, tabooProb jump x n y * ENNReal.ofReal (rate y)⁻¹ ≤
        tabooProb jump x n y * ENNReal.ofReal r0⁻¹ := by
      intro n y
      gcongr
      exact hr y
    calc ∑' n, ∑' y, tabooProb jump x n y * ENNReal.ofReal (rate y)⁻¹
        ≤ ∑' n, ∑' y, tabooProb jump x n y * ENNReal.ofReal r0⁻¹ :=
          ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun y => hb n y
      _ = (∑' n, mass jump x n) * ENNReal.ofReal r0⁻¹ := by
          simp_rw [ENNReal.tsum_mul_right]; rfl
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hm) ENNReal.ofReal_lt_top

open Classical in
lemma good_step (s t : X) (hs : Good jump s) (hp : 0 < jump s t) : Good jump t := by
  by_cases hst : t = s
  · subst hst; exact hs
  obtain ⟨h, hfin, hsup⟩ := hs
  set q := jump s t with hq
  have hq0 : q ≠ 0 := hp.ne'
  have hqt : q ≠ ⊤ := PMF.apply_ne_top _ _
  set K := h s / q with hKdef
  have hK : K ≠ ⊤ := ENNReal.div_ne_top (hfin s) hq0
  have hKq : K * q = h s := ENNReal.div_mul_cancel hq0 hqt
  let y : X → ℝ≥0∞ := fun i => if i = s then K else h i + K
  refine ⟨y, ?_, ?_⟩
  · intro i
    simp only [y]
    split_ifs
    · exact hK
    · exact ENNReal.add_ne_top.2 ⟨hfin i, hK⟩
  · intro i
    have hterm : ∀ k, cc jump t i k * y k ≤ cc jump s i k * h k + cc jump t i k * K := by
      intro k
      simp only [y, cc]
      by_cases hkt : k = t
      · simp [hkt]
      · by_cases hks : k = s
        · subst hks; simp [hkt]
        · simp [hkt, hks, mul_add]
    have hA := c_split jump t i
    set A := ∑' k, cc jump t i k
    have hA1 : A ≤ 1 := by rw [← hA]; exact le_add_self
    have hbound : 1 + ∑' k, cc jump t i k * y k ≤ h i + A * K := by
      calc 1 + ∑' k, cc jump t i k * y k
          ≤ 1 + ∑' k, (cc jump s i k * h k + cc jump t i k * K) := by
            gcongr with k; exact hterm k
        _ = (1 + ∑' k, cc jump s i k * h k) + A * K := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, add_assoc]
        _ ≤ h i + A * K := by gcongr; exact hsup i
    refine hbound.trans ?_
    by_cases his : i = s
    · subst his
      simp only [y, if_true]
      have : K = (q + A) * K := by rw [hq, hA, one_mul]
      refine le_of_eq ?_
      calc h i + A * K = K * q + A * K := by rw [hKq]
        _ = (q + A) * K := by ring
        _ = K := this.symm
    · simp only [y, if_neg his]
      gcongr
      exact mul_le_of_le_one_left (by simp) hA1

lemma propagate (Q : X → Prop) (hQ : ∀ a b, Q a → 0 < jump a b → Q b) :
    ∀ n a b, Q a → 0 < stepIter jump n a b → Q b := by
  intro n
  induction n with
  | zero =>
    intro a b ha hs
    simp only [stepIter, PMF.pure_apply] at hs
    split_ifs at hs with h
    · subst h; exact ha
    · exact absurd hs (lt_irrefl 0)
  | succ n ih =>
    intro a b ha hs
    simp only [stepIter, PMF.bind_apply] at hs
    obtain ⟨k, hk⟩ : ∃ k, 0 < jump a k * stepIter jump n k b := by
      by_contra hc
      push Not at hc
      have : ∑' k, jump a k * stepIter jump n k b = 0 :=
        ENNReal.tsum_eq_zero.2 (fun k => nonpos_iff_eq_zero.1 (hc k))
      rw [this] at hs; exact lt_irrefl 0 hs
    have h1 : 0 < jump a k := pos_of_ne_zero (left_ne_zero_of_mul hk.ne')
    have h2 : 0 < stepIter jump n k b := pos_of_ne_zero (right_ne_zero_of_mul hk.ne')
    exact ih k b (hQ a k ha h1) h2

open Classical in
/-- Foster drift toward the single state `x` gives a Good witness. -/
lemma good_of_drift (x : X) (V : X → ℝ≥0∞) (hV : ∀ y, y ≠ x → V y ≠ ⊤)
    (hx : ∑' z, jump x z * V z ≠ ⊤)
    (hdrift : ∀ y, y ≠ x → 1 + ∑' z, jump y z * V z ≤ V y) : Good jump x := by
  let h : X → ℝ≥0∞ := fun y => if y = x then 1 + ∑' z, cc jump x x z * V z else V y
  have hc : ∀ y, ∑' z, cc jump x y z * h z = ∑' z, cc jump x y z * V z := by
    intro y; congr 1; funext z
    simp only [h, cc]; split_ifs <;> simp_all
  have hle : ∀ y, ∑' z, cc jump x y z * V z ≤ ∑' z, jump y z * V z := by
    intro y; apply ENNReal.tsum_le_tsum; intro z
    simp only [cc]; split_ifs <;> simp
  refine ⟨h, ?_, ?_⟩
  · intro y; simp only [h]; split_ifs with hy
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ne_top_of_le_ne_top hx (hle x)⟩
    · exact hV y hy
  · intro y; rw [hc]
    by_cases hy : y = x
    · subst hy; simp [h]
    · simp only [h, if_neg hy]
      exact le_trans (add_le_add_right (hle y) 1) (hdrift y hy)

end TF50

namespace PS50

open RedundancyStab.IID Finset

lemma bind_pure_tsum {ι Y : Type*} [Fintype ι] (p : PMF ι) (next : ι → Y) (V : Y → ℝ≥0∞) :
    ∑' z, (p.bind (fun i => PMF.pure (next i))) z * V z = ∑ i, p i * V (next i) := by
  classical
  have hp : ∀ a : Y, ∑' z, (PMF.pure a) z * V z = V a := by
    intro a
    rw [tsum_eq_single a]
    · simp
    · intro z hz; simp [PMF.pure_apply, hz]
  calc ∑' z, (p.bind (fun i => PMF.pure (next i))) z * V z
      = ∑' z, ∑' i, p i * ((PMF.pure (next i)) z * V z) := by
        congr 1; funext z
        rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
        congr 1; funext i; ring
    _ = ∑' i, p i * ∑' z, (PMF.pure (next i)) z * V z := by
        rw [ENNReal.tsum_comm]; congr 1; funext i; rw [ENNReal.tsum_mul_left]
    _ = ∑ i, p i * V (next i) := by simp_rw [hp]; rw [tsum_fintype]

lemma clock_tsum {ι Y : Type*} [Fintype ι] (r : ι → ℝ) (next : ι → Y) (x : Y)
    (h0 : ∀ i, 0 ≤ r i) (hpos : 0 < ∑ i, r i) (V : Y → ℝ≥0∞) :
    ∑' z, clockStep r (fun i => PMF.pure (next i)) x z * V z =
      ∑ i, ENNReal.ofReal (r i / ∑ j, r j) * V (next i) := by
  unfold clockStep
  rw [dif_pos ⟨h0, hpos⟩, bind_pure_tsum]
  simp [PMF.ofFintype_apply]

lemma clock_pos {ι Y : Type*} [Fintype ι] (r : ι → ℝ) (next : ι → Y) (x : Y)
    (h0 : ∀ i, 0 ≤ r i) (hpos : 0 < ∑ i, r i) (i : ι) (hi : 0 < r i) :
    0 < clockStep r (fun i => PMF.pure (next i)) x (next i) := by
  unfold clockStep
  rw [dif_pos ⟨h0, hpos⟩, PMF.bind_apply]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum i)
  simp only [PMF.ofFintype_apply, PMF.pure_apply, if_true, mul_one]
  exact ENNReal.ofReal_pos.2 (div_pos hi hpos)

lemma good_of_gen {ι Y : Type*} [Fintype ι] (jump : Y → PMF Y) (r : Y → ι → ℝ)
    (next : Y → ι → Y)
    (hj : ∀ y, jump y = clockStep (r y) (fun i => PMF.pure (next y i)) y)
    (h0 : ∀ y i, 0 ≤ r y i) (hpos : ∀ y, 0 < ∑ i, r y i)
    (W : Y → ℝ) (hW : ∀ y, 0 ≤ W y) (x : Y)
    (hdr : ∀ y, y ≠ x → ∑ i, r y i * (W (next y i) - W y) ≤ -∑ i, r y i) :
    TF50.Good jump x := by
  have hq : ∀ y i, 0 ≤ r y i / (∑ j, r y j) := fun y i => div_nonneg (h0 y i) (hpos y).le
  have key : ∀ y, ∑' z, jump y z * ENNReal.ofReal (W z) =
      ENNReal.ofReal (∑ i, r y i / (∑ j, r y j) * W (next y i)) := by
    intro y
    rw [hj, clock_tsum _ _ _ (h0 y) (hpos y),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hq y i) (hW _))]
    congr 1; funext i; rw [ENNReal.ofReal_mul (hq y i)]
  apply TF50.good_of_drift jump x (fun z => ENNReal.ofReal (W z)) (fun _ _ => ENNReal.ofReal_ne_top)
  · rw [key]; exact ENNReal.ofReal_ne_top
  · intro y hy
    rw [key, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
      (Finset.sum_nonneg fun i _ => mul_nonneg (hq y i) (hW _))]
    apply ENNReal.ofReal_le_ofReal
    have hR := hpos y
    have h1 := hdr y hy
    set R := ∑ j, r y j with hRdef
    have e1 : ∑ i, r y i / R * W (next y i) = (∑ i, r y i * W (next y i)) / R := by
      rw [Finset.sum_div]; congr 1; funext i; ring
    have e2 : ∑ i, r y i * (W (next y i) - W y) = ∑ i, r y i * W (next y i) - R * W y := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]; rfl
    have : (∑ i, r y i * W (next y i)) / R ≤ W y - 1 := by
      rw [div_le_iff₀ hR]; nlinarith [e2, h1]
    linarith

variable {K d : ℕ}

lemma copies_cast (n : PSState K d) (s : Fin K) :
    (copies K d n s : ℝ) = ∑ c ∈ typesAt K d s, (n c : ℝ) := by
  simp [copies]

lemma swap_sum (f : JobType K d → Fin K → ℝ) :
    ∑ s, ∑ c ∈ typesAt K d s, f c s = ∑ c, ∑ s ∈ c.1, f c s := by
  classical
  calc ∑ s, ∑ c ∈ typesAt K d s, f c s = ∑ s, ∑ c, if s ∈ c.1 then f c s else 0 := by
        simp only [typesAt, Finset.sum_filter]
    _ = ∑ c, ∑ s, if s ∈ c.1 then f c s else 0 := Finset.sum_comm
    _ = ∑ c, ∑ s ∈ c.1, f c s := by
        congr 1; funext c; rw [← Finset.sum_filter]; congr 1; ext s; simp

lemma sum_copies (n : PSState K d) :
    ∑ s, (copies K d n s : ℝ) = d * ∑ c, (n c : ℝ) := by
  simp_rw [copies_cast]
  rw [swap_sum (fun c _ => (n c : ℝ)), Finset.mul_sum]
  congr 1; funext c
  rw [Finset.sum_const, c.2, nsmul_eq_mul]

lemma busy_eq (n : PSState K d) (s : Fin K) :
    ∑ c ∈ typesAt K d s, (n c : ℝ) / (copies K d n s : ℝ) =
      if copies K d n s = 0 then 0 else 1 := by
  rw [← Finset.sum_div, ← copies_cast]
  split_ifs with h
  · simp [h]
  · exact div_self (by exact_mod_cast h)

lemma dep_total (n : PSState K d) :
    ∑ c, ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ) =
      ∑ s, (if copies K d n s = 0 then (0:ℝ) else 1) := by
  rw [← swap_sum (fun c s => (n c : ℝ) / (copies K d n s : ℝ))]
  congr 1; funext s; exact busy_eq n s

lemma card_types_at (hd : 1 ≤ d) (s : Fin K) :
    (typesAt K d s).card = (K - 1).choose (d - 1) := by
  classical
  have hK : 1 ≤ K := by have := s.2; omega
  have e : (Finset.powersetCard (d - 1) ((univ : Finset (Fin K)).erase s)).card =
      (K - 1).choose (d - 1) := by
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem (mem_univ s), card_univ, Fintype.card_fin]
  rw [← e]
  refine Finset.card_bij (fun c _ => c.1.erase s) ?_ ?_ ?_
  · intro c hc
    simp only [typesAt, mem_filter, mem_univ, true_and] at hc
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset_erase s (subset_univ _), ?_⟩
    rw [Finset.card_erase_of_mem hc, c.2]
  · intro a ha b hb hab
    simp only [typesAt, mem_filter, mem_univ, true_and] at ha hb
    apply Subtype.ext
    rw [← Finset.insert_erase ha, ← Finset.insert_erase hb, hab]
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    have hst : s ∉ t := fun h => by have := ht.1 h; simp at this
    refine ⟨⟨insert s t, by rw [Finset.card_insert_of_notMem hst, ht.2]; omega⟩, ?_, ?_⟩
    · simp [typesAt]
    · simp [Finset.erase_insert hst]

end PS50

namespace PS50

open RedundancyStab.IID Finset

variable {K d : ℕ}

lemma copies_update (n : PSState K d) (c : JobType K d) (v : ℕ) (s : Fin K) :
    (copies K d (Function.update n c v) s : ℝ) =
      copies K d n s + (if s ∈ c.1 then (v : ℝ) - n c else 0) := by
  rw [copies_cast, copies_cast]
  split_ifs with hs
  · have hc : c ∈ typesAt K d s := by simp [typesAt, hs]
    rw [← Finset.add_sum_erase _ _ hc, ← Finset.add_sum_erase _ _ hc, Function.update_self]
    have : ∑ x ∈ (typesAt K d s).erase c, ((Function.update n c v x : ℕ) : ℝ) =
        ∑ x ∈ (typesAt K d s).erase c, (n x : ℝ) :=
      Finset.sum_congr rfl (fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
    rw [this]; ring
  · have hc : c ∉ typesAt K d s := by simp [typesAt, hs]
    rw [add_zero]
    exact Finset.sum_congr rfl (fun x hx => by
      rw [Function.update_of_ne (show x ≠ c by rintro rfl; exact hc hx)])

lemma tot_update (n : PSState K d) (c : JobType K d) (v : ℕ) :
    ∑ c', ((Function.update n c v c' : ℕ) : ℝ) = ∑ c', (n c' : ℝ) + ((v : ℝ) - n c) := by
  rw [← Finset.add_sum_erase _ _ (mem_univ c), ← Finset.add_sum_erase _ _ (mem_univ c),
    Function.update_self]
  have : ∑ x ∈ univ.erase c, ((Function.update n c v x : ℕ) : ℝ) = ∑ x ∈ univ.erase c, (n x : ℝ) :=
    Finset.sum_congr rfl (fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
  rw [this]; ring

/-- the quadratic Lyapunov function `Σ_s M_s²` -/
noncomputable def Phi (n : PSState K d) : ℝ := ∑ s, (copies K d n s : ℝ) ^ 2

lemma phi_update (n : PSState K d) (c : JobType K d) (v : ℕ) :
    Phi (Function.update n c v) = Phi n +
      ∑ s ∈ c.1, (2 * ((v : ℝ) - n c) * copies K d n s + ((v : ℝ) - n c) ^ 2) := by
  unfold Phi
  simp_rw [copies_update]
  have : ∀ s, ((copies K d n s : ℝ) + if s ∈ c.1 then (v : ℝ) - n c else 0) ^ 2 =
      (copies K d n s : ℝ) ^ 2 + if s ∈ c.1 then
        2 * ((v : ℝ) - n c) * copies K d n s + ((v : ℝ) - n c) ^ 2 else 0 := by
    intro s; split_ifs <;> ring
  simp_rw [this, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib]

end PS50

namespace PS50

open RedundancyStab.IID Finset

variable {K d : ℕ}

lemma cauchy_inv (c : Finset (Fin K)) (f : Fin K → ℝ) (hf : ∀ s ∈ c, 0 < f s) :
    (c.card : ℝ) ^ 2 ≤ (∑ s ∈ c, 1 / f s) * ∑ s ∈ c, f s := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq c (fun s => Real.sqrt (1 / f s))
    (fun s => Real.sqrt (f s))
  have e1 : ∑ s ∈ c, Real.sqrt (1 / f s) * Real.sqrt (f s) = c.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have := hf s hs
    rw [← Real.sqrt_mul (by positivity), one_div, inv_mul_cancel₀ this.ne', Real.sqrt_one]
  have e2 : ∑ s ∈ c, Real.sqrt (1 / f s) ^ 2 = ∑ s ∈ c, 1 / f s :=
    Finset.sum_congr rfl (fun s hs => Real.sq_sqrt (by have := hf s hs; positivity))
  have e3 : ∑ s ∈ c, Real.sqrt (f s) ^ 2 = ∑ s ∈ c, f s :=
    Finset.sum_congr rfl (fun s hs => Real.sq_sqrt (hf s hs).le)
  rw [e1, e2, e3] at h; exact h

lemma le_copies (n : PSState K d) (c : JobType K d) (s : Fin K) (hs : s ∈ c.1) :
    n c ≤ copies K d n s := by
  have hc : c ∈ typesAt K d s := by simp [typesAt, hs]
  unfold copies
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) hc

lemma dep_c (n : PSState K d) (c : JobType K d) (μ : ℝ) (hμ : 0 ≤ μ) :
    μ * (∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ)) *
      (Phi (Function.update n c (n c - 1)) - Phi n) ≤
      μ * (d : ℝ) ^ 2 - 2 * μ * (d : ℝ) ^ 2 * (n c : ℝ) := by
  by_cases h0 : n c = 0
  · simp [h0]; positivity
  have h1 : 1 ≤ n c := Nat.one_le_iff_ne_zero.2 h0
  set M : Fin K → ℝ := fun s => (copies K d n s : ℝ) with hMdef
  have hM : ∀ s ∈ c.1, (n c : ℝ) ≤ M s := fun s hs => by
    simp only [M]; exact_mod_cast le_copies n c s hs
  have hn1 : (1 : ℝ) ≤ n c := by exact_mod_cast h1
  have hMpos : ∀ s ∈ c.1, 0 < M s := fun s hs => by linarith [hM s hs]
  rw [phi_update]
  have hv : (((n c - 1 : ℕ) : ℝ) - n c) = -1 := by rw [Nat.cast_sub h1]; ring
  rw [hv, add_sub_cancel_left]
  have e1 : ∑ s ∈ c.1, (2 * (-1 : ℝ) * (copies K d n s : ℝ) + (-1) ^ 2) =
      (d : ℝ) - 2 * ∑ s ∈ c.1, M s := by
    have : ∀ s, 2 * (-1 : ℝ) * (copies K d n s : ℝ) + (-1) ^ 2 = 1 - 2 * M s := by
      intro s; simp only [M]; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_const, c.2, Finset.mul_sum]
    simp
  rw [e1]
  set a := ∑ s ∈ c.1, 1 / M s with ha
  set b := ∑ s ∈ c.1, M s with hb
  have hsum : ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ) = (n c : ℝ) * a := by
    rw [ha, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [M]; ring
  have hna : (n c : ℝ) * a ≤ d := by
    rw [← hsum]
    calc ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ) ≤ ∑ s ∈ c.1, (1 : ℝ) :=
          Finset.sum_le_sum (fun s hs => (div_le_one (hMpos s hs)).2 (hM s hs))
      _ = d := by simp [c.2]
  have hab : (d : ℝ) ^ 2 ≤ a * b := by
    have := cauchy_inv c.1 M hMpos
    rw [c.2] at this; exact this
  rw [hsum]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ n c := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hna (mul_nonneg hμ hd0),
    mul_le_mul_of_nonneg_left hab (mul_nonneg hμ hn0)]

lemma arr_phi (n : PSState K d) (hd : 1 ≤ d) :
    ∑ c : JobType K d, (Phi (Function.update n c (n c + 1)) - Phi n) =
      ((K - 1).choose (d - 1) : ℝ) * (2 * d * ∑ c, (n c : ℝ) + K) := by
  have h1 : ∀ c : JobType K d, Phi (Function.update n c (n c + 1)) - Phi n =
      ∑ s ∈ c.1, (2 * (copies K d n s : ℝ) + 1) := by
    intro c
    rw [phi_update]
    have : (((n c + 1 : ℕ) : ℝ) - n c) = 1 := by push_cast; ring
    rw [this, add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  simp_rw [h1]
  have hs := swap_sum (K := K) (d := d) (fun _ s => 2 * (copies K d n s : ℝ) + 1)
  rw [← hs]
  simp_rw [Finset.sum_const, card_types_at hd, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_copies]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]; ring

lemma choose_rel (hd : 1 ≤ d) (hdK : d ≤ K) :
    ((K - 1).choose (d - 1) : ℝ) * K = (K.choose d : ℝ) * d := by
  have h := Nat.add_one_mul_choose_eq (K - 1) (d - 1)
  have hK : K - 1 + 1 = K := by omega
  have hd' : d - 1 + 1 = d := by omega
  rw [hK, hd'] at h
  have : ((K - 1).choose (d - 1) * K : ℕ) = (K.choose d * d : ℕ) := by rw [mul_comm, h]
  exact_mod_cast this

lemma card_jobtype : Fintype.card (JobType K d) = K.choose d := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

lemma arr_rate_sum (hdK : d ≤ K) (lam : ℝ) :
    ∑ _c : JobType K d, lam / (K.choose d : ℝ) = lam := by
  rw [Finset.sum_const, Finset.card_univ, card_jobtype, nsmul_eq_mul]
  have : (K.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdK).ne'
  field_simp

/-- total departure intensity (number of busy servers) -/
noncomputable def Dn (n : PSState K d) : ℝ :=
  ∑ c, ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ)

lemma Dn_le (n : PSState K d) : Dn n ≤ K := by
  unfold Dn; rw [dep_total]
  calc ∑ s : Fin K, (if copies K d n s = 0 then (0 : ℝ) else 1) ≤ ∑ _s : Fin K, (1 : ℝ) :=
        Finset.sum_le_sum (fun s _ => by split_ifs <;> norm_num)
    _ = K := by simp

lemma Dn_nonneg (n : PSState K d) : 0 ≤ Dn n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)

lemma Dn_ge (hd : 1 ≤ d) (n : PSState K d) (c : JobType K d) (hc : 1 ≤ n c) : 1 ≤ Dn n := by
  unfold Dn; rw [dep_total]
  obtain ⟨s, hs⟩ : c.1.Nonempty := by
    rw [← Finset.card_pos, c.2]; omega
  have hM : copies K d n s ≠ 0 := by have := le_copies n c s hs; omega
  calc (1 : ℝ) = if copies K d n s = 0 then (0 : ℝ) else 1 := by rw [if_neg hM]
    _ ≤ _ := Finset.single_le_sum (f := fun s => if copies K d n s = 0 then (0 : ℝ) else 1)
          (fun s _ => by split_ifs <;> norm_num) (Finset.mem_univ s)

noncomputable def Tn (n : PSState K d) : ℕ := ∑ c, n c

lemma Tn_update (n : PSState K d) (c : JobType K d) (v : ℕ) :
    Tn (Function.update n c v) + n c = Tn n + v := by
  have h := tot_update n c v
  have : ((Tn (Function.update n c v) + n c : ℕ) : ℝ) = ((Tn n + v : ℕ) : ℝ) := by
    simp only [Tn]; push_cast; rw [h]; ring
  exact_mod_cast this

lemma Tn_cast (n : PSState K d) : (Tn n : ℝ) = ∑ c, (n c : ℝ) := by
  simp [Tn]

noncomputable def W (B θ : ℝ) (n : PSState K d) : ℝ := Phi n + B * (1 - θ ^ Tn n)

end PS50

namespace PS50

open RedundancyStab.IID Finset

variable {K d : ℕ}

lemma rate_eq (hdK : d ≤ K) (lam μ : ℝ) (n : PSState K d) :
    ∑ e, psEventRate K d lam μ n e = lam + μ * Dn n := by
  rw [Fintype.sum_sum_type]
  simp only [psEventRate]
  rw [arr_rate_sum hdK, ← Finset.mul_sum]
  rfl

lemma ps_drift (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hμ : 0 ≤ μ)
    (B θ : ℝ) (n : PSState K d) (t : ℕ) (ht : Tn n = t + 1) :
    ∑ e, psEventRate K d lam μ n e * (W B θ (psApply K d n e) - W B θ n) ≤
      lam * d + μ * d ^ 2 * (K.choose d : ℝ) - 2 * d ^ 2 * (μ - lam / K) * (Tn n : ℝ)
      + B * (1 - θ) * θ ^ t * (lam * θ - μ * Dn n) := by
  rw [Fintype.sum_sum_type]
  simp only [psEventRate, psApply]
  have hTa : ∀ c : JobType K d, Tn (Function.update n c (n c + 1)) = t + 2 := by
    intro c; have := Tn_update n c (n c + 1); omega
  have harr : ∀ c : JobType K d, lam / (K.choose d : ℝ) *
      (W B θ (Function.update n c (n c + 1)) - W B θ n) =
      lam / (K.choose d : ℝ) * (Phi (Function.update n c (n c + 1)) - Phi n) +
      lam / (K.choose d : ℝ) * (B * (θ ^ (t + 1) - θ ^ (t + 2))) := by
    intro c; simp only [W, hTa c, ht]; ring
  have hdep : ∀ c : JobType K d, μ * (∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ)) *
      (W B θ (Function.update n c (n c - 1)) - W B θ n) ≤
      μ * (d : ℝ) ^ 2 - 2 * μ * (d : ℝ) ^ 2 * (n c : ℝ) -
      B * (1 - θ) * θ ^ t * (μ * ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ)) := by
    intro c
    have h1 := dep_c n c μ hμ
    by_cases h0 : n c = 0
    · simp [h0]; positivity
    · have hTd : Tn (Function.update n c (n c - 1)) = t := by
        have := Tn_update n c (n c - 1); omega
      have e : W B θ (Function.update n c (n c - 1)) - W B θ n =
          (Phi (Function.update n c (n c - 1)) - Phi n) - B * (1 - θ) * θ ^ t := by
        simp only [W, hTd, ht]; ring
      rw [e]
      nlinarith [h1]
  rw [Finset.sum_congr rfl (fun c _ => harr c), Finset.sum_add_distrib]
  have hA1 : ∑ c : JobType K d, lam / (K.choose d : ℝ) *
      (Phi (Function.update n c (n c + 1)) - Phi n) =
      lam * d + 2 * lam * d ^ 2 / K * (Tn n : ℝ) := by
    rw [← Finset.mul_sum, arr_phi n hd, ← Tn_cast]
    have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    have hC : (K.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdK).ne'
    have hX : ((K - 1).choose (d - 1) : ℝ) = (K.choose d : ℝ) * d / K := by
      rw [eq_div_iff hK, choose_rel hd hdK]
    rw [hX]; field_simp; ring
  have hA2 : ∑ c : JobType K d, lam / (K.choose d : ℝ) * (B * (θ ^ (t + 1) - θ ^ (t + 2))) =
      lam * (B * (θ ^ (t + 1) - θ ^ (t + 2))) := by
    rw [← Finset.sum_mul, arr_rate_sum hdK]
  have hD : ∑ c : JobType K d, (μ * (d : ℝ) ^ 2 - 2 * μ * (d : ℝ) ^ 2 * (n c : ℝ) -
      B * (1 - θ) * θ ^ t * (μ * ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ))) =
      μ * d ^ 2 * (K.choose d : ℝ) - 2 * μ * d ^ 2 * (Tn n : ℝ) - B * (1 - θ) * θ ^ t * (μ * Dn n) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      card_jobtype, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Tn_cast]
    unfold Dn; ring
  have hdsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (JobType K d))) => hdep c)
  rw [hD] at hdsum
  rw [hA1, hA2]
  have hθe : lam * (B * (θ ^ (t + 1) - θ ^ (t + 2))) = B * (1 - θ) * θ ^ t * (lam * θ) := by ring
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have e2 : 2 * lam * (d : ℝ) ^ 2 / K * (Tn n : ℝ) = 2 * d ^ 2 * (lam / K) * (Tn n : ℝ) := by
    field_simp
  rw [hθe, e2]
  nlinarith [hdsum]

lemma ps_good0 (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hρ : lam / (μ * K) < 1) : TF50.Good (psJump K d lam μ) (0 : PSState K d) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlamK : lam < μ * K := by rwa [div_lt_one (by positivity)] at hρ
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = μ / (2 * lam + 2 * μ) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_iff₀ (by positivity)]; linarith
  have hlθ : lam * θ ≤ μ / 2 := by
    rw [hθ, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = lam * d + μ * d ^ 2 * (K.choose d : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 2 * d ^ 2 * (μ - lam / K) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    have h1 : lam / K < μ := by rw [div_lt_iff₀ hK]; linarith
    have h2 := sub_pos.2 h1
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    rw [hδ]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = lam + μ * K := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0]; positivity
  have hR0 : 0 < R := by rw [hR]; positivity
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = ⌈(C0 + R) / δ⌉₊ := ⟨_, rfl⟩
  have hN0' : C0 + R ≤ δ * N0 := by
    have := Nat.le_ceil ((C0 + R) / δ)
    rw [← hN0, div_le_iff₀ hδ0] at this; linarith
  have hθN : 0 < θ ^ N0 := pow_pos hθ0 _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * (C0 + R) / (μ * θ ^ N0) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBθ : B * θ ^ N0 * (μ / 4) = C0 + R := by rw [hB]; field_simp
  have h0 : ∀ (y : PSState K d) (i : PSEvent K d), 0 ≤ psEventRate K d lam μ y i := by
    intro y i
    cases i with
    | inl c => exact div_nonneg hlam.le (Nat.cast_nonneg _)
    | inr c =>
      exact mul_nonneg hμ.le (Finset.sum_nonneg fun _ _ =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine good_of_gen (psJump K d lam μ) (psEventRate K d lam μ) (psApply K d) (fun _ => rfl)
    h0 ?_ (W B θ) ?_ 0 ?_
  · intro y; rw [rate_eq hdK]; nlinarith [Dn_nonneg y]
  · intro y
    have hP : 0 ≤ Phi y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hp : θ ^ Tn y ≤ 1 := pow_le_one₀ hθ0.le (by linarith)
    unfold W; nlinarith
  · intro y hy
    obtain ⟨c, hc⟩ : ∃ c, 1 ≤ y c := by
      by_contra h; push Not at h
      exact hy (funext fun c => by have := h c; simp only [Pi.zero_apply]; omega)
    obtain ⟨t, ht⟩ : ∃ t, Tn y = t + 1 := by
      have : y c ≤ Tn y := Finset.single_le_sum (f := y) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)
      exact ⟨Tn y - 1, by omega⟩
    have hdr := ps_drift hd hdK lam μ hμ.le B θ y t ht
    rw [← hC0, ← hδ] at hdr
    rw [rate_eq hdK]
    have hD1 := Dn_ge hd y c hc
    have hDK := Dn_le y
    have hθt : 0 < θ ^ t := pow_pos hθ0 _
    have hb : lam * θ - μ * Dn y ≤ -(μ / 2) := by nlinarith
    have ha : 0 ≤ (1 - θ) - 1 / 2 := by linarith
    have hab := mul_le_mul_of_nonneg_left hb ha
    have hg1 : (1 - θ) * (lam * θ - μ * Dn y) ≤ -(μ / 4) := by
      nlinarith [mul_nonneg ha hμ.le]
    have hg : B * (1 - θ) * θ ^ t * (lam * θ - μ * Dn y) ≤ -(B * θ ^ t * (μ / 4)) := by
      have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg hB0 hθt.le)
      nlinarith
    have hT : ((Tn y : ℕ) : ℝ) = t + 1 := by rw [ht]; push_cast; ring
    have hμD : μ * Dn y ≤ μ * K := mul_le_mul_of_nonneg_left hDK hμ.le
    by_cases hcase : N0 ≤ t + 1
    · have h1 : (N0 : ℝ) ≤ (Tn y : ℝ) := by rw [ht]; exact_mod_cast hcase
      have h2 := mul_le_mul_of_nonneg_left h1 hδ0.le
      have hBt : 0 ≤ B * θ ^ t * (μ / 4) :=
        mul_nonneg (mul_nonneg hB0 hθt.le) (by positivity)
      linarith
    · have htN : t ≤ N0 := by omega
      have hpow : θ ^ N0 ≤ θ ^ t := pow_le_pow_of_le_one hθ0.le (by linarith) htN
      have h3 : B * θ ^ N0 * (μ / 4) ≤ B * θ ^ t * (μ / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB0) (by positivity)
      have hTn : 0 ≤ δ * ((Tn y : ℕ) : ℝ) := mul_nonneg hδ0.le (Nat.cast_nonneg _)
      linarith

lemma ps_good_all (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hρ : lam / (μ * K) < 1) :
    ∀ N, ∀ n : PSState K d, Tn n = N → TF50.Good (psJump K d lam μ) n := by
  intro N
  induction N with
  | zero =>
    intro n hn
    have : n = 0 := by
      funext c
      have := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      simp only [Pi.zero_apply]; unfold Tn at hn; omega
    subst this; exact ps_good0 hd hdK lam μ hlam hμ hρ
  | succ N ih =>
    intro n hn
    obtain ⟨c, hc⟩ : ∃ c, 1 ≤ n c := by
      by_contra h; push Not at h
      have : Tn n = 0 := Finset.sum_eq_zero (fun c _ => by have := h c; omega)
      omega
    have hm : Tn (Function.update n c (n c - 1)) = N := by
      have := Tn_update n c (n c - 1); omega
    have hmn : psApply K d (Function.update n c (n c - 1)) (Sum.inl c) = n := by
      simp only [psApply, Function.update_self, Function.update_idem]
      rw [Nat.sub_add_cancel hc, Function.update_eq_self]
    have h0 : ∀ i, 0 ≤ psEventRate K d lam μ (Function.update n c (n c - 1)) i := by
      intro i
      cases i with
      | inl c => exact div_nonneg hlam.le (Nat.cast_nonneg _)
      | inr c =>
        exact mul_nonneg hμ.le (Finset.sum_nonneg fun _ _ =>
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hpos : 0 < ∑ i, psEventRate K d lam μ (Function.update n c (n c - 1)) i := by
      rw [rate_eq hdK]; nlinarith [Dn_nonneg (Function.update n c (n c - 1))]
    have hp := clock_pos (psEventRate K d lam μ (Function.update n c (n c - 1)))
      (psApply K d (Function.update n c (n c - 1))) (Function.update n c (n c - 1)) h0 hpos
      (Sum.inl c) (by
        simp only [psEventRate]
        exact div_pos hlam (by exact_mod_cast Nat.choose_pos hdK))
    rw [hmn] at hp
    exact TF50.good_step _ _ n (ih _ hm) hp

lemma ps_posrec (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hρ : lam / (μ * K) < 1) : PositiveRecurrent (psJump K d lam μ) (psRate K d lam μ) := by
  intro n
  refine TF50.posrec_of_good _ _ lam hlam (fun y => ?_) n
    (ps_good_all hd hdK lam μ hlam hμ hρ (Tn n) n rfl)
  unfold psRate
  rw [rate_eq hdK]; nlinarith [Dn_nonneg y]

end PS50

namespace TF50

variable {X : Type*} (jump : X → PMF X)

/-- Lyapunov witness for target `x`, required only on a transition-closed set `Q`. -/
def GoodOn (Q : X → Prop) (x : X) : Prop :=
  ∃ h : X → ℝ≥0∞, (∀ y, Q y → h y ≠ ⊤) ∧ ∀ y, Q y → 1 + ∑' z, cc jump x y z * h z ≤ h y

lemma taboo_support (Q : X → Prop) (hQ : ∀ a b, Q a → 0 < jump a b → Q b) (x : X) (hx : Q x) :
    ∀ n y, tabooProb jump x n y ≠ 0 → Q y := by
  intro n
  induction n with
  | zero =>
    intro y hy
    simp only [tabooProb] at hy
    split_ifs at hy with h
    · subst h; exact hx
    · exact absurd rfl hy
  | succ n ih =>
    intro y hy
    simp only [tabooProb] at hy
    split_ifs at hy with h
    · exact absurd rfl hy
    · obtain ⟨z, hz⟩ : ∃ z, tabooProb jump x n z * jump z y ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hy (ENNReal.tsum_eq_zero.2 hc)
      exact hQ z y (ih z (left_ne_zero_of_mul hz)) (pos_of_ne_zero (right_ne_zero_of_mul hz))

lemma teleOn (Q : X → Prop) (hQ : ∀ a b, Q a → 0 < jump a b → Q b) (x : X) (hx : Q x)
    (h : X → ℝ≥0∞) (hsup : ∀ y, Q y → 1 + ∑' z, cc jump x y z * h z ≤ h y) :
    ∀ N, ∑ n ∈ Finset.range N, mass jump x n +
      ∑' y, tabooProb jump x N y * h y ≤ h x := by
  have step : ∀ n, mass jump x n + ∑' y, tabooProb jump x (n + 1) y * h y ≤
      ∑' y, tabooProb jump x n y * h y := by
    intro n
    unfold mass
    simp_rw [taboo_succ, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    rw [← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum; intro z
    by_cases hz : tabooProb jump x n z = 0
    · simp [hz]
    calc tabooProb jump x n z + tabooProb jump x n z * ∑' y, cc jump x z y * h y
        = tabooProb jump x n z * (1 + ∑' y, cc jump x z y * h y) := by ring
      _ ≤ tabooProb jump x n z * h z := by
          gcongr; exact hsup z (taboo_support jump Q hQ x hx n z hz)
  intro N
  induction N with
  | zero => simp [taboo_zero_mul]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc]
    calc _ ≤ ∑ n ∈ Finset.range N, mass jump x n + ∑' y, tabooProb jump x N y * h y := by
          gcongr; exact step N
      _ ≤ h x := ih

lemma posrec_of_goodOn (Q : X → Prop) (hQ : ∀ a b, Q a → 0 < jump a b → Q b)
    (rate : X → ℝ) (r0 : ℝ) (hr0 : 0 < r0) (hr : ∀ y, r0 ≤ rate y)
    (x : X) (hx : Q x) (hg : GoodOn jump Q x) :
    Recurrent jump x ∧ meanReturnTime jump rate x < ⊤ := by
  obtain ⟨h, hfin, hsup⟩ := hg
  have hmle : ∑' n, mass jump x n ≤ h x :=
    ENNReal.tsum_le_of_sum_range_le (fun N => le_trans le_self_add (teleOn jump Q hQ x hx h hsup N))
  have hm : ∑' n, mass jump x n ≠ ⊤ := ne_top_of_le_ne_top (hfin x hx) hmle
  constructor
  · unfold Recurrent
    have hle : ∑' n, firstReturnProb jump x n ≤ 1 :=
      ENNReal.tsum_le_of_sum_range_le (fun N => by
        rw [← frp_partial jump x N]; exact le_self_add)
    refine le_antisymm hle ?_
    have ht : Tendsto (fun N => mass jump x N) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hm
    have ht2 : Tendsto (fun N => 1 - mass jump x N) atTop (𝓝 (1 - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds ht (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at ht2
    refine le_of_tendsto' ht2 (fun N => ?_)
    calc 1 - mass jump x N = ∑ n ∈ Finset.range N, firstReturnProb jump x n := by
          rw [← frp_partial jump x N]
          exact ENNReal.add_sub_cancel_right (ne_top_of_le_ne_top ENNReal.one_ne_top
            (by rw [← frp_partial jump x N]; exact le_add_self))
      _ ≤ _ := ENNReal.sum_le_tsum _
  · unfold meanReturnTime
    have hb : ∀ n y, tabooProb jump x n y * ENNReal.ofReal (rate y)⁻¹ ≤
        tabooProb jump x n y * ENNReal.ofReal r0⁻¹ := by
      intro n y
      gcongr
      exact hr y
    calc ∑' n, ∑' y, tabooProb jump x n y * ENNReal.ofReal (rate y)⁻¹
        ≤ ∑' n, ∑' y, tabooProb jump x n y * ENNReal.ofReal r0⁻¹ :=
          ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun y => hb n y
      _ = (∑' n, mass jump x n) * ENNReal.ofReal r0⁻¹ := by
          simp_rw [ENNReal.tsum_mul_right]; rfl
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hm) ENNReal.ofReal_lt_top

open Classical in
lemma good_stepOn (Q : X → Prop) (s t : X) (hQs : Q s) (hs : GoodOn jump Q s)
    (hp : 0 < jump s t) : GoodOn jump Q t := by
  by_cases hst : t = s
  · subst hst; exact hs
  obtain ⟨h, hfin, hsup⟩ := hs
  set q := jump s t with hq
  have hq0 : q ≠ 0 := hp.ne'
  have hqt : q ≠ ⊤ := PMF.apply_ne_top _ _
  set K := h s / q with hKdef
  have hK : K ≠ ⊤ := ENNReal.div_ne_top (hfin s hQs) hq0
  have hKq : K * q = h s := ENNReal.div_mul_cancel hq0 hqt
  let y : X → ℝ≥0∞ := fun i => if i = s then K else h i + K
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    simp only [y]
    split_ifs
    · exact hK
    · exact ENNReal.add_ne_top.2 ⟨hfin i hi, hK⟩
  · intro i hi
    have hterm : ∀ k, cc jump t i k * y k ≤ cc jump s i k * h k + cc jump t i k * K := by
      intro k
      simp only [y, cc]
      by_cases hkt : k = t
      · simp [hkt]
      · by_cases hks : k = s
        · subst hks; simp [hkt]
        · simp [hkt, hks, mul_add]
    have hA := c_split jump t i
    set A := ∑' k, cc jump t i k
    have hA1 : A ≤ 1 := by rw [← hA]; exact le_add_self
    have hbound : 1 + ∑' k, cc jump t i k * y k ≤ h i + A * K := by
      calc 1 + ∑' k, cc jump t i k * y k
          ≤ 1 + ∑' k, (cc jump s i k * h k + cc jump t i k * K) := by
            gcongr with k; exact hterm k
        _ = (1 + ∑' k, cc jump s i k * h k) + A * K := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, add_assoc]
        _ ≤ h i + A * K := by gcongr; exact hsup i hi
    refine hbound.trans ?_
    by_cases his : i = s
    · subst his
      simp only [y, if_true]
      have : K = (q + A) * K := by rw [hq, hA, one_mul]
      refine le_of_eq ?_
      calc h i + A * K = K * q + A * K := by rw [hKq]
        _ = (q + A) * K := by ring
        _ = K := this.symm
    · simp only [y, if_neg his]
      gcongr
      exact mul_le_of_le_one_left (by simp) hA1

open Classical in
/-- Foster drift toward `x`, only on a transition-closed set `Q`. -/
lemma good_of_driftOn (Q : X → Prop) (hQ : ∀ a b, Q a → 0 < jump a b → Q b)
    (x : X) (V : X → ℝ≥0∞) (hV : ∀ y, Q y → y ≠ x → V y ≠ ⊤)
    (hx : ∑' z, jump x z * V z ≠ ⊤)
    (hdrift : ∀ y, Q y → y ≠ x → 1 + ∑' z, jump y z * V z ≤ V y) : GoodOn jump Q x := by
  let h : X → ℝ≥0∞ := fun y => if y = x then 1 + ∑' z, cc jump x x z * V z else V y
  have hc : ∀ y, ∑' z, cc jump x y z * h z = ∑' z, cc jump x y z * V z := by
    intro y; congr 1; funext z
    simp only [h, cc]; split_ifs <;> simp_all
  have hle : ∀ y, ∑' z, cc jump x y z * V z ≤ ∑' z, jump y z * V z := by
    intro y; apply ENNReal.tsum_le_tsum; intro z
    simp only [cc]; split_ifs <;> simp
  refine ⟨h, ?_, ?_⟩
  · intro y hy; simp only [h]; split_ifs with hyx
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ne_top_of_le_ne_top hx (hle x)⟩
    · exact hV y hy hyx
  · intro y hy; rw [hc]
    by_cases hyx : y = x
    · subst hyx; simp [h]
    · simp only [h, if_neg hyx]
      exact le_trans (add_le_add_right (hle y) 1) (hdrift y hy hyx)

end TF50

namespace ROS50

open RedundancyStab.IID Finset

variable {K d : ℕ}

lemma add_apply (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (c' : JobType K d)
    (A' : Finset (Fin K)) :
    rosAdd K d k c A c' A' = k c' A' + if c' = c ∧ A' = A then 1 else 0 := by
  unfold rosAdd
  by_cases hc : c' = c
  · subst hc
    by_cases hA : A' = A
    · subst hA; simp
    · simp [hA]
  · simp [hc]

lemma remove_apply (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (h : 1 ≤ k c A)
    (c' : JobType K d) (A' : Finset (Fin K)) :
    rosRemove K d k c A c' A' + (if c' = c ∧ A' = A then 1 else 0) = k c' A' := by
  unfold rosRemove
  by_cases hc : c' = c
  · subst hc
    by_cases hA : A' = A
    · subst hA; simp; omega
    · simp [hA]
  · simp [hc]

lemma ind_busy (c : JobType K d) (A : Finset (Fin K)) (s : Fin K) :
    ∑ c' : JobType K d, ∑ A' ∈ univ.filter (fun A : Finset (Fin K) => s ∈ A),
      (if c' = c ∧ A' = A then 1 else 0) = if s ∈ A then 1 else 0 := by
  simp [ite_and, Finset.sum_ite_eq', Finset.mem_filter]

lemma ind_jobs (c : JobType K d) (A : Finset (Fin K)) (c' : JobType K d) :
    ∑ A' : Finset (Fin K), (if c' = c ∧ A' = A then 1 else 0) = if c' = c then 1 else 0 := by
  by_cases h : c' = c <;> simp [h]

lemma busy_add (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (s : Fin K) :
    rosBusy K d (rosAdd K d k c A) s = rosBusy K d k s + if s ∈ A then 1 else 0 := by
  unfold rosBusy
  simp_rw [add_apply, Finset.sum_add_distrib]
  rw [ind_busy]

lemma busy_remove (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (h : 1 ≤ k c A)
    (s : Fin K) :
    rosBusy K d (rosRemove K d k c A) s + (if s ∈ A then 1 else 0) = rosBusy K d k s := by
  unfold rosBusy
  rw [← ind_busy c A s, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, remove_apply k c A h]

lemma jobs_add (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (c' : JobType K d) :
    rosJobs K d (rosAdd K d k c A) c' = rosJobs K d k c' + if c' = c then 1 else 0 := by
  unfold rosJobs
  simp_rw [add_apply, Finset.sum_add_distrib]
  rw [ind_jobs]

lemma jobs_remove (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (h : 1 ≤ k c A)
    (c' : JobType K d) :
    rosJobs K d (rosRemove K d k c A) c' + (if c' = c then 1 else 0) = rosJobs K d k c' := by
  unfold rosJobs
  rw [← ind_jobs c A c', ← Finset.sum_add_distrib]
  simp_rw [remove_apply k c A h]

/-- invariant with a set `L` of freed servers still to refill -/
def InvL (L : Finset (Fin K)) (k : RosState K d) : Prop :=
  (∀ c A, ¬ A ⊆ c.1 → k c A = 0) ∧ (∀ s, rosBusy K d k s ≤ 1) ∧
  (∀ s, s ∉ L → rosBusy K d k s = 0 → ∀ c ∈ typesAt K d s, rosJobs K d k c = 0) ∧
  (∀ s ∈ L, rosBusy K d k s = 0)

lemma busy_pos_of (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (s : Fin K)
    (hs : s ∈ A) (h : 1 ≤ k c A) : 1 ≤ rosBusy K d k s := by
  unfold rosBusy
  calc 1 ≤ k c A := h
    _ ≤ ∑ A' ∈ univ.filter (fun A : Finset (Fin K) => s ∈ A), k c A' :=
        Finset.single_le_sum (f := fun A' => k c A') (fun _ _ => Nat.zero_le _)
          (by simp [hs])
    _ ≤ _ := Finset.single_le_sum
        (f := fun c' => ∑ A' ∈ univ.filter (fun A : Finset (Fin K) => s ∈ A), k c' A')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

lemma inv_arrive (k : RosState K d) (hk : InvL ∅ k) (c : JobType K d) :
    InvL ∅ (rosArrive K d k c) := by
  obtain ⟨h1, h2, h3, -⟩ := hk
  unfold rosArrive
  set A := c.1.filter (fun s => rosBusy K d k s = 0) with hA
  refine ⟨?_, ?_, ?_, by simp⟩
  · intro c' A' hA'
    rw [add_apply, h1 c' A' hA']
    simp only [zero_add, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    rintro rfl rfl; exact hA' (Finset.filter_subset _ _)
  · intro s
    rw [busy_add]
    split_ifs with hs
    · rw [hA, Finset.mem_filter] at hs; rw [hs.2]
    · simpa using h2 s
  · intro s _ hs c' hc'
    rw [busy_add] at hs
    have hs0 : rosBusy K d k s = 0 := by omega
    have hsA : s ∉ A := by intro h; rw [if_pos h] at hs; omega
    rw [jobs_add, h3 s (by simp) hs0 c' hc']
    have : c' ≠ c := by
      rintro rfl
      apply hsA
      simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
      rw [hA, Finset.mem_filter]; exact ⟨hc', hs0⟩
    simp [this]

lemma inv_remove (k : RosState K d) (hk : InvL ∅ k) (c : JobType K d) (A : Finset (Fin K))
    (h : 1 ≤ k c A) : InvL A (rosRemove K d k c A) := by
  obtain ⟨h1, h2, h3, -⟩ := hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c' A' hA'
    have := remove_apply k c A h c' A'
    rw [h1 c' A' hA'] at this; omega
  · intro s; have := busy_remove k c A h s; have := h2 s; omega
  · intro s hsA hs c' hc'
    have e := busy_remove k c A h s
    rw [if_neg hsA, add_zero] at e
    have hj := jobs_remove k c A h c'
    have := h3 s (by simp) (by rw [← e]; exact hs) c' hc'
    omega
  · intro s hs
    have e := busy_remove k c A h s
    rw [if_pos hs] at e
    have := h2 s
    have := busy_pos_of k c A s hs h
    omega

end ROS50

namespace ROS50

open RedundancyStab.IID Finset

variable {K d : ℕ}

lemma busy_start (k : RosState K d) (s : Fin K) (c : JobType K d) (A : Finset (Fin K))
    (hsA : s ∉ A) (h : 1 ≤ k c A) (s' : Fin K) :
    rosBusy K d (rosStartAt K d k s c A) s' = rosBusy K d k s' + if s' = s then 1 else 0 := by
  unfold rosStartAt
  rw [busy_add]
  have e := busy_remove k c A h s'
  by_cases h1 : s' = s
  · subst h1; simp only [Finset.mem_insert, true_or, if_true, if_neg hsA] at e ⊢; omega
  · by_cases h2 : s' ∈ A
    · simp only [Finset.mem_insert, h1, h2, false_or, if_true, if_false] at e ⊢; omega
    · simp only [Finset.mem_insert, h1, h2, or_self, if_false] at e ⊢; omega

lemma jobs_start (k : RosState K d) (s : Fin K) (c : JobType K d) (A : Finset (Fin K))
    (h : 1 ≤ k c A) (c' : JobType K d) :
    rosJobs K d (rosStartAt K d k s c A) c' = rosJobs K d k c' := by
  unfold rosStartAt
  rw [jobs_add]
  have := jobs_remove k c A h c'
  omega

lemma zero_of_busy_zero (k : RosState K d) (s : Fin K) (hs : rosBusy K d k s = 0)
    (c : JobType K d) (A : Finset (Fin K)) (hA : s ∈ A) : k c A = 0 := by
  by_contra h
  have := busy_pos_of k c A s hA (Nat.one_le_iff_ne_zero.2 h)
  omega

lemma inv_start (L : Finset (Fin K)) (k : RosState K d) (hk : InvL L k) (s : Fin K) (hsL : s ∈ L)
    (c : JobType K d) (A : Finset (Fin K)) (hsc : s ∈ c.1) (hsA : s ∉ A) (h : 1 ≤ k c A) :
    InvL (L.erase s) (rosStartAt K d k s c A) := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  have hAc : A ⊆ c.1 := by
    by_contra hn; have := h1 c A hn; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c' A' hA'
    unfold rosStartAt
    rw [add_apply]
    have e := remove_apply k c A h c' A'
    rw [h1 c' A' hA'] at e
    have : ¬ (c' = c ∧ A' = insert s A) := by
      rintro ⟨rfl, rfl⟩; exact hA' (Finset.insert_subset hsc hAc)
    rw [if_neg this]; omega
  · intro s'
    rw [busy_start k s c A hsA h]
    split_ifs with hs'
    · subst hs'; rw [h4 s' hsL]
    · simpa using h2 s'
  · intro s'' hs'' hb c' hc'
    rw [busy_start k s c A hsA h] at hb
    have hne : s'' ≠ s := by intro he; rw [if_pos he] at hb; omega
    rw [if_neg hne, add_zero] at hb
    have hL : s'' ∉ L := fun hm => hs'' (Finset.mem_erase.2 ⟨hne, hm⟩)
    rw [jobs_start k s c A h]
    exact h3 s'' hL hb c' hc'
  · intro s' hs'
    obtain ⟨hne, hm⟩ := Finset.mem_erase.1 hs'
    rw [busy_start k s c A hsA h, if_neg hne, add_zero]
    exact h4 s' hm

lemma inv_stay (L : Finset (Fin K)) (k : RosState K d) (hk : InvL L k) (s : Fin K) (hsL : s ∈ L)
    (hw : ∀ p, rosWaitWeight K d k s p = 0) : InvL (L.erase s) k := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  refine ⟨h1, h2, ?_, fun s' hs' => h4 s' (Finset.mem_of_mem_erase hs')⟩
  intro s'' hs'' hb c' hc'
  by_cases he : s'' = s
  · subst he
    unfold rosJobs
    refine Finset.sum_eq_zero (fun A _ => ?_)
    by_cases hA : s'' ∈ A
    · exact zero_of_busy_zero k s'' hb c' A hA
    · have := hw (c', A)
      simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
      simpa [rosWaitWeight, hc', hA] using this
  · exact h3 s'' (fun hm => hs'' (Finset.mem_erase.2 ⟨he, hm⟩)) hb c' hc'

lemma pick_support (k : RosState K d) (s : Fin K) (z : RosState K d)
    (hz : rosPick K d k s z ≠ 0) :
    (z = k ∧ ∀ p, rosWaitWeight K d k s p = 0) ∨
      ∃ c A, s ∈ c.1 ∧ s ∉ A ∧ 1 ≤ k c A ∧ z = rosStartAt K d k s c A := by
  classical
  unfold rosPick at hz
  split_ifs at hz with h
  · right
    have hz' : z ∈ (PMF.map (fun p : JobType K d × Finset (Fin K) => rosStartAt K d k s p.1 p.2)
        (PMF.normalize (rosWaitWeight K d k s) _ _)).support := (PMF.mem_support_iff _ _).2 hz
    rw [PMF.support_map, PMF.support_normalize] at hz'
    obtain ⟨⟨c, A⟩, hp, rfl⟩ := hz'
    simp only [Function.mem_support, rosWaitWeight] at hp
    split_ifs at hp with hc
    · refine ⟨c, A, hc.1, hc.2, ?_, rfl⟩
      exact Nat.one_le_iff_ne_zero.2 (by exact_mod_cast hp)
    · exact absurd rfl hp
  · left
    have hz' : z = k := by
      by_contra hne; exact hz (by simp [PMF.pure_apply, hne])
    refine ⟨hz', ?_⟩
    have hfin : ∑ p, rosWaitWeight K d k s p ≠ ⊤ := by
      refine ENNReal.sum_ne_top.2 (fun p _ => ?_)
      unfold rosWaitWeight; split_ifs <;> simp
    have h0 : ∑ p, rosWaitWeight K d k s p = 0 := by
      by_contra hne; exact h ⟨hne, hfin⟩
    intro p
    exact (Finset.sum_eq_zero_iff.1 h0) p (Finset.mem_univ p)

lemma inv_refill : ∀ (l : List (Fin K)), l.Nodup → ∀ (k : RosState K d), InvL l.toFinset k →
    ∀ z, rosRefill K d l k z ≠ 0 → InvL ∅ z := by
  intro l
  induction l with
  | nil =>
    intro _ k hk z hz
    simp only [rosRefill, PMF.pure_apply] at hz
    split_ifs at hz with h
    · subst h; simpa using hk
    · exact absurd rfl hz
  | cons s l ih =>
    intro hnd k hk z hz
    rw [List.nodup_cons] at hnd
    simp only [rosRefill, PMF.bind_apply] at hz
    obtain ⟨y, hy⟩ : ∃ y, rosPick K d k s y * rosRefill K d l y z ≠ 0 := by
      by_contra hc; push Not at hc; exact hz (ENNReal.tsum_eq_zero.2 hc)
    have hy1 := left_ne_zero_of_mul hy
    have hy2 := right_ne_zero_of_mul hy
    have hsL : s ∈ (s :: l).toFinset := by simp
    have herase : ((s :: l).toFinset).erase s = l.toFinset := by
      rw [List.toFinset_cons, Finset.erase_insert (by simpa using hnd.1)]
    rcases pick_support k s y hy1 with ⟨rfl, hw⟩ | ⟨c, A, hsc, hsA, h1, rfl⟩
    · have := inv_stay _ y hk s hsL hw
      rw [herase] at this
      exact ih hnd.2 y this z hy2
    · have := inv_start _ k hk s hsL c A hsc hsA h1
      rw [herase] at this
      exact ih hnd.2 _ this z hy2

lemma inv_closed (lam μ : ℝ) : ∀ a b : RosState K d, InvL ∅ a → 0 < rosJump K d lam μ a b →
    InvL ∅ b := by
  intro a b ha hb
  unfold rosJump clockStep at hb
  split_ifs at hb with hc
  · rw [PMF.bind_apply] at hb
    obtain ⟨e, he⟩ : ∃ e, (PMF.ofFintype _ (sum_ofReal_div_total _ hc.1 hc.2)) e *
        rosNext K d a e b ≠ 0 := by
      by_contra h; push Not at h; rw [ENNReal.tsum_eq_zero.2 h] at hb; exact lt_irrefl 0 hb
    have he1 := left_ne_zero_of_mul he
    have he2 := right_ne_zero_of_mul he
    rw [PMF.ofFintype_apply] at he1
    have hr : 0 < rosEventRate K d lam μ a e := by
      by_contra hn; push Not at hn
      apply he1
      rw [ENNReal.ofReal_eq_zero]
      exact div_nonpos_of_nonpos_of_nonneg hn hc.2.le
    cases e with
    | inl c =>
      simp only [rosNext, PMF.pure_apply] at he2
      split_ifs at he2 with h
      · subst h; exact inv_arrive a ha c
      · exact absurd rfl he2
    | inr p =>
      obtain ⟨c, A⟩ := p
      simp only [rosEventRate] at hr
      have hk : 1 ≤ a c A := by
        by_contra hn; push Not at hn
        have : a c A = 0 := by omega
        rw [this] at hr; simp at hr
      simp only [rosNext] at he2
      have hinv := inv_remove a ha c A hk
      have e : (A.sort (· ≤ ·)).toFinset = A := by simp
      have hinv' : InvL (A.sort (· ≤ ·)).toFinset (rosRemove K d a c A) := by rw [e]; exact hinv
      exact inv_refill _ (Finset.sort_nodup _ _) _ hinv' b he2
  · simp only [PMF.pure_apply] at hb
    split_ifs at hb with h
    · subst h; exact ha
    · exact absurd hb (lt_irrefl 0)

lemma inv_empty : InvL ∅ (rosEmpty K d) := by
  refine ⟨fun _ _ _ => rfl, fun s => ?_, fun s _ _ c _ => ?_, by simp⟩
  · simp [rosBusy, rosEmpty]
  · simp [rosJobs, rosEmpty]

end ROS50

namespace ROS50

open RedundancyStab.IID Finset

variable {K d : ℕ}

lemma ros_rate_ge (hdK : d ≤ K) (lam μ : ℝ) (hμ : 0 ≤ μ) (k : RosState K d) :
    lam ≤ rosRate K d lam μ k := by
  unfold rosRate
  rw [Fintype.sum_sum_type]
  simp only [rosEventRate]
  rw [PS50.arr_rate_sum hdK]
  have : 0 ≤ ∑ p : JobType K d × Finset (Fin K), μ * (p.2.card : ℝ) * (k p.1 p.2 : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  linarith

/-- The ROS conjunct follows from a Foster witness at the empty state on the invariant set. -/
lemma ros_conj_of_good (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hG : TF50.GoodOn (rosJump K d lam μ) (InvL ∅) (rosEmpty K d)) :
    ∀ x : RosState K d, (∃ m : ℕ, 0 < stepIter (rosJump K d lam μ) m (rosEmpty K d) x) →
      Recurrent (rosJump K d lam μ) x ∧
        meanReturnTime (rosJump K d lam μ) (rosRate K d lam μ) x < ⊤ := by
  rintro x ⟨m, hm⟩
  have hP := TF50.propagate (rosJump K d lam μ)
    (fun y => InvL ∅ y ∧ TF50.GoodOn (rosJump K d lam μ) (InvL ∅) y)
    (fun a b ha hab => ⟨inv_closed lam μ a b ha.1 hab,
      TF50.good_stepOn _ _ a b ha.1 ha.2 hab⟩)
    m (rosEmpty K d) x ⟨inv_empty, hG⟩ hm
  exact TF50.posrec_of_goodOn _ (InvL ∅) (inv_closed lam μ) (rosRate K d lam μ) lam hlam
    (ros_rate_ge hdK lam μ hμ.le) x hP.1 hP.2

end ROS50

namespace PS50

open RedundancyStab.IID Finset

lemma bind_tsum' {α Y : Type*} (p : PMF α) (f : α → PMF Y) (V : Y → ℝ≥0∞) :
    ∑' z, (p.bind f) z * V z = ∑' a, p a * ∑' z, f a z * V z := by
  calc ∑' z, (p.bind f) z * V z = ∑' z, ∑' a, p a * (f a z * V z) := by
        congr 1; funext z
        rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
        congr 1; funext a; ring
    _ = ∑' a, p a * ∑' z, f a z * V z := by
        rw [ENNReal.tsum_comm]; congr 1; funext a; rw [ENNReal.tsum_mul_left]

/-- Generator drift with PMF-valued transitions on a closed set `Q` gives `GoodOn`. -/
lemma good_of_genOn {ι Y : Type*} [Fintype ι] (jump : Y → PMF Y) (r : Y → ι → ℝ)
    (next : Y → ι → PMF Y) (hj : ∀ y, jump y = clockStep (r y) (next y) y)
    (h0 : ∀ y i, 0 ≤ r y i) (hpos : ∀ y, 0 < ∑ i, r y i)
    (Q : Y → Prop) (hQ : ∀ a b, Q a → 0 < jump a b → Q b)
    (W : Y → ℝ) (EW : Y → ι → ℝ)
    (hE : ∀ y i, Q y → 0 < r y i → ∑' z, next y i z * ENNReal.ofReal (W z) ≤ ENNReal.ofReal (EW y i))
    (hE0 : ∀ y i, Q y → 0 < r y i → 0 ≤ EW y i)
    (x : Y) (hx : Q x)
    (hdr : ∀ y, Q y → y ≠ x → ∑ i, r y i * (EW y i - W y) ≤ -∑ i, r y i) :
    TF50.GoodOn jump Q x := by
  have hq : ∀ y i, 0 ≤ r y i / (∑ j, r y j) := fun y i => div_nonneg (h0 y i) (hpos y).le
  have key : ∀ y, Q y → ∑' z, jump y z * ENNReal.ofReal (W z) ≤
      ENNReal.ofReal (∑ i, r y i / (∑ j, r y j) * EW y i) := by
    intro y hy
    rw [hj, clockStep, dif_pos ⟨h0 y, hpos y⟩, bind_tsum', tsum_fintype]
    have hnn : ∀ i, 0 ≤ r y i / (∑ j, r y j) * EW y i := by
      intro i
      rcases (h0 y i).lt_or_eq with hi | hi
      · exact mul_nonneg (hq y i) (hE0 y i hy hi)
      · rw [← hi, zero_div, zero_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i)]
    refine Finset.sum_le_sum (fun i _ => ?_)
    simp only [PMF.ofFintype_apply]
    rcases (h0 y i).lt_or_eq with hi | hi
    · rw [ENNReal.ofReal_mul (hq y i)]
      gcongr
      exact hE y i hy hi
    · rw [← hi, zero_div, ENNReal.ofReal_zero, zero_mul]; exact zero_le
  apply TF50.good_of_driftOn jump Q hQ x (fun z => ENNReal.ofReal (W z))
    (fun _ _ _ => ENNReal.ofReal_ne_top)
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (key x hx)
  · intro y hy hyx
    refine le_trans (add_le_add_right (key y hy) 1) ?_
    have hsum : 0 ≤ ∑ i, r y i / (∑ j, r y j) * EW y i := by
      refine Finset.sum_nonneg (fun i _ => ?_)
      rcases (h0 y i).lt_or_eq with hi | hi
      · exact mul_nonneg (hq y i) (hE0 y i hy hi)
      · rw [← hi, zero_div, zero_mul]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hsum]
    apply ENNReal.ofReal_le_ofReal
    have hR := hpos y
    have h1 := hdr y hy hyx
    set R := ∑ j, r y j with hRdef
    have e1 : ∑ i, r y i / R * EW y i = (∑ i, r y i * EW y i) / R := by
      rw [Finset.sum_div]; congr 1; funext i; ring
    have e2 : ∑ i, r y i * (EW y i - W y) = ∑ i, r y i * EW y i - R * W y := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]; rfl
    have : (∑ i, r y i * EW y i) / R ≤ W y - 1 := by
      rw [div_le_iff₀ hR]; nlinarith [e2, h1]
    linarith

end PS50

namespace ROS50

open RedundancyStab.IID Finset PS50

variable {K d : ℕ}

/-- piecewise-linear cutoff: 0 below ε/2, 1 above ε -/
noncomputable def psi (ε u : ℝ) : ℝ := min 1 (max 0 ((u - ε / 2) / (ε / 2)))

lemma psi_nonneg (ε u : ℝ) : 0 ≤ psi ε u := le_min zero_le_one (le_max_left _ _)
lemma psi_le_one (ε u : ℝ) : psi ε u ≤ 1 := min_le_left _ _
lemma psi_eq_one (ε u : ℝ) (hε : 0 < ε) (hu : ε ≤ u) : psi ε u = 1 := by
  unfold psi
  apply min_eq_left
  apply le_max_of_le_right
  rw [le_div_iff₀ (by linarith)]; linarith

/-- `S_c = Σ_{s∈c} M_s` -/
noncomputable def Sc (n : PSState K d) (c : JobType K d) : ℝ := ∑ s ∈ c.1, (copies K d n s : ℝ)

noncomputable def chi (ε : ℝ) (n : PSState K d) (c : JobType K d) : ℝ :=
  ∏ l ∈ c.1, psi ε ((copies K d n l : ℝ) / (Tn n : ℝ))

noncomputable def rr (ε : ℝ) (n : PSState K d) (c : JobType K d) : ℝ := Sc n c * chi ε n c

noncomputable def rbar (ε : ℝ) (n : PSState K d) (s : Fin K) : ℝ :=
  ∑ c ∈ typesAt K d s, (n c : ℝ) / (copies K d n s : ℝ) * rr ε n c

lemma chi_nonneg (ε : ℝ) (n : PSState K d) (c : JobType K d) : 0 ≤ chi ε n c :=
  Finset.prod_nonneg fun _ _ => psi_nonneg _ _

lemma chi_le_one (ε : ℝ) (n : PSState K d) (c : JobType K d) : chi ε n c ≤ 1 :=
  Finset.prod_le_one (fun _ _ => psi_nonneg _ _) (fun _ _ => psi_le_one _ _)

lemma Sc_nonneg (n : PSState K d) (c : JobType K d) : 0 ≤ Sc n c :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma rr_nonneg (ε : ℝ) (n : PSState K d) (c : JobType K d) : 0 ≤ rr ε n c :=
  mul_nonneg (Sc_nonneg n c) (chi_nonneg ε n c)

lemma rr_le_Sc (ε : ℝ) (n : PSState K d) (c : JobType K d) : rr ε n c ≤ Sc n c :=
  mul_le_of_le_one_right (Sc_nonneg n c) (chi_le_one ε n c)

lemma rbar_nonneg (ε : ℝ) (n : PSState K d) (s : Fin K) : 0 ≤ rbar ε n s :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (rr_nonneg _ _ _)

lemma one_sub_prod_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hp0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hp1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi)) (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have haj0 := h0 j (Finset.mem_insert_self j s)
    have haj1 := h1 j (Finset.mem_insert_self j s)
    nlinarith

/-- Cauchy step: `Σ_s r̄_s ≥ d² Σ_c n_c χ_c`. -/
lemma rbar_sum_ge (ε : ℝ) (n : PSState K d) :
    (d : ℝ) ^ 2 * ∑ c, (n c : ℝ) * chi ε n c ≤ ∑ s, rbar ε n s := by
  unfold rbar
  rw [swap_sum (fun c s => (n c : ℝ) / (copies K d n s : ℝ) * rr ε n c), Finset.mul_sum]
  refine Finset.sum_le_sum (fun c _ => ?_)
  by_cases h0 : n c = 0
  · simp [h0]
  have h1 : 1 ≤ n c := Nat.one_le_iff_ne_zero.2 h0
  have hMpos : ∀ s ∈ c.1, (0 : ℝ) < copies K d n s := fun s hs => by
    have := le_copies n c s hs; exact_mod_cast (by omega : 0 < copies K d n s)
  have hc := cauchy_inv c.1 (fun s => (copies K d n s : ℝ)) hMpos
  rw [c.2] at hc
  have e : ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ) * rr ε n c =
      ((n c : ℝ) * chi ε n c) * ((∑ s ∈ c.1, 1 / (copies K d n s : ℝ)) * Sc n c) := by
    rw [rr, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [e]
  have hnc : 0 ≤ (n c : ℝ) * chi ε n c := mul_nonneg (Nat.cast_nonneg _) (chi_nonneg _ _ _)
  calc (d : ℝ) ^ 2 * ((n c : ℝ) * chi ε n c) = ((n c : ℝ) * chi ε n c) * (d : ℝ) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [Sc] using hc) hnc

/-- mass outside the all-high types is at most `K ε T` -/
lemma low_mass_le (ε : ℝ) (hε : 0 < ε) (n : PSState K d) :
    ∑ c, (n c : ℝ) * (1 - chi ε n c) ≤ K * ε * (Tn n : ℝ) := by
  have step1 : ∀ c, (n c : ℝ) * (1 - chi ε n c) ≤
      ∑ l ∈ c.1, (n c : ℝ) * (1 - psi ε ((copies K d n l : ℝ) / (Tn n : ℝ))) := by
    intro c
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (one_sub_prod_le _ _ (fun _ _ => psi_nonneg _ _)
      (fun _ _ => psi_le_one _ _)) (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum fun c _ => step1 c).trans ?_
  rw [← swap_sum (fun c l => (n c : ℝ) * (1 - psi ε ((copies K d n l : ℝ) / (Tn n : ℝ))))]
  have hl : ∀ l : Fin K, ∑ c ∈ typesAt K d l,
      (n c : ℝ) * (1 - psi ε ((copies K d n l : ℝ) / (Tn n : ℝ))) ≤ ε * (Tn n : ℝ) := by
    intro l
    rw [← Finset.sum_mul, ← copies_cast]
    have hT : (0 : ℝ) ≤ Tn n := Nat.cast_nonneg _
    by_cases hb : ε * (Tn n : ℝ) ≤ (copies K d n l : ℝ)
    · have hpos : 0 < (Tn n : ℝ) ∨ (Tn n : ℝ) = 0 := hT.lt_or_eq.imp id Eq.symm
      rcases hpos with hpos | hz
      · rw [psi_eq_one ε _ hε (by rw [le_div_iff₀ hpos]; linarith), sub_self, mul_zero]
        positivity
      · have : (copies K d n l : ℝ) ≤ Tn n := by
          rw [copies_cast, Tn_cast]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.cast_nonneg _)
        rw [hz] at this ⊢
        have h0 : (copies K d n l : ℝ) = 0 := le_antisymm this (Nat.cast_nonneg _)
        rw [h0, zero_mul]; simp
    · push Not at hb
      calc (copies K d n l : ℝ) * (1 - psi ε ((copies K d n l : ℝ) / (Tn n : ℝ)))
          ≤ (copies K d n l : ℝ) * 1 := by
            gcongr; linarith [psi_nonneg ε ((copies K d n l : ℝ) / (Tn n : ℝ))]
        _ ≤ ε * Tn n := by linarith
  calc ∑ l : Fin K, ∑ c ∈ typesAt K d l,
        (n c : ℝ) * (1 - psi ε ((copies K d n l : ℝ) / (Tn n : ℝ)))
      ≤ ∑ _l : Fin K, ε * (Tn n : ℝ) := Finset.sum_le_sum fun l _ => hl l
    _ = K * ε * (Tn n : ℝ) := by simp; ring

/-- `Σ_s r̄_s ≥ d² T (1 − K ε)` -/
lemma rbar_sum_ge' (ε : ℝ) (hε : 0 < ε) (n : PSState K d) :
    (d : ℝ) ^ 2 * ((Tn n : ℝ) - K * ε * (Tn n : ℝ)) ≤ ∑ s, rbar ε n s := by
  refine le_trans ?_ (rbar_sum_ge ε n)
  have h := low_mass_le ε hε n
  have e : ∑ c, (n c : ℝ) * chi ε n c = (Tn n : ℝ) - ∑ c, (n c : ℝ) * (1 - chi ε n c) := by
    rw [Tn_cast, ← Finset.sum_sub_distrib]; congr 1; funext c; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

end ROS50

namespace ROS50

open RedundancyStab.IID Finset PS50

variable {K d : ℕ}

lemma copies_le_T (n : PSState K d) (s : Fin K) : (copies K d n s : ℝ) ≤ Tn n := by
  rw [copies_cast, Tn_cast]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Nat.cast_nonneg _)

lemma Sc_le (n : PSState K d) (c : JobType K d) : Sc n c ≤ d * Tn n := by
  unfold Sc
  calc ∑ s ∈ c.1, (copies K d n s : ℝ) ≤ ∑ _s ∈ c.1, (Tn n : ℝ) :=
        Finset.sum_le_sum (fun s _ => copies_le_T n s)
    _ = d * Tn n := by rw [Finset.sum_const, c.2, nsmul_eq_mul]

lemma psi_le (ε u : ℝ) (hε : 0 < ε) (hu : 0 ≤ u) : ε * psi ε u ≤ 2 * u := by
  have h1 : psi ε u ≤ max 0 ((u - ε / 2) / (ε / 2)) := min_le_right _ _
  have h2 : (u - ε / 2) / (ε / 2) = 2 * u / ε - 1 := by field_simp
  have h3 : max 0 ((u - ε / 2) / (ε / 2)) ≤ 2 * u / ε :=
    max_le (by positivity) (by rw [h2]; linarith)
  calc ε * psi ε u ≤ ε * (2 * u / ε) := mul_le_mul_of_nonneg_left (h1.trans h3) hε.le
    _ = 2 * u := by field_simp

lemma chi_le_psi (ε : ℝ) (n : PSState K d) (c : JobType K d) (s : Fin K) (hs : s ∈ c.1) :
    chi ε n c ≤ psi ε ((copies K d n s : ℝ) / (Tn n : ℝ)) := by
  unfold chi
  rw [← Finset.mul_prod_erase _ _ hs]
  exact mul_le_of_le_one_right (psi_nonneg _ _)
    (Finset.prod_le_one (fun _ _ => psi_nonneg _ _) (fun _ _ => psi_le_one _ _))

lemma rr_le_M (ε : ℝ) (hε : 0 < ε) (n : PSState K d) (c : JobType K d) (s : Fin K)
    (hs : s ∈ c.1) : ε * rr ε n c ≤ 2 * d * (copies K d n s : ℝ) := by
  have hM : (0 : ℝ) ≤ copies K d n s := Nat.cast_nonneg _
  have hT : (0 : ℝ) ≤ Tn n := Nat.cast_nonneg _
  have h2 : ε * chi ε n c ≤ 2 * ((copies K d n s : ℝ) / (Tn n : ℝ)) :=
    (mul_le_mul_of_nonneg_left (chi_le_psi ε n c s hs) hε.le).trans
      (psi_le ε _ hε (div_nonneg hM hT))
  have h3 : Sc n c * ((copies K d n s : ℝ) / (Tn n : ℝ)) ≤ d * (copies K d n s : ℝ) := by
    by_cases hT0 : (Tn n : ℝ) = 0
    · rw [hT0, div_zero, mul_zero]; positivity
    · calc Sc n c * ((copies K d n s : ℝ) / (Tn n : ℝ))
          ≤ (d * Tn n) * ((copies K d n s : ℝ) / (Tn n : ℝ)) :=
            mul_le_mul_of_nonneg_right (Sc_le n c) (div_nonneg hM hT)
        _ = d * (copies K d n s : ℝ) := by field_simp
  calc ε * rr ε n c = Sc n c * (ε * chi ε n c) := by unfold rr; ring
    _ ≤ Sc n c * (2 * ((copies K d n s : ℝ) / (Tn n : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (Sc_nonneg n c)
    _ ≤ 2 * d * (copies K d n s : ℝ) := by nlinarith [h3]

lemma mem_of_typesAt {s : Fin K} {c : JobType K d} (hc : c ∈ typesAt K d s) : s ∈ c.1 := by
  simpa [typesAt] using hc

lemma rbar_le (ε : ℝ) (hε : 0 < ε) (n : PSState K d) (s : Fin K) :
    ε * rbar ε n s ≤ 2 * d * (copies K d n s : ℝ) := by
  by_cases hM : (copies K d n s : ℝ) = 0
  · unfold rbar; simp [hM]
  · unfold rbar
    rw [Finset.mul_sum]
    calc ∑ c ∈ typesAt K d s, ε * ((n c : ℝ) / (copies K d n s : ℝ) * rr ε n c)
        ≤ ∑ c ∈ typesAt K d s, (n c : ℝ) / (copies K d n s : ℝ) *
            (2 * d * (copies K d n s : ℝ)) := by
          refine Finset.sum_le_sum (fun c hc => ?_)
          have := rr_le_M ε hε n c s (mem_of_typesAt hc)
          have hq : 0 ≤ (n c : ℝ) / (copies K d n s : ℝ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this hq]
      _ = 2 * d * (copies K d n s : ℝ) := by
          rw [copies_cast] at hM ⊢
          rw [← Finset.sum_mul, ← Finset.sum_div]
          field_simp

/-- the service-correction coefficient of an in-service class `(c, A)` -/
noncomputable def gg (ε : ℝ) (n : PSState K d) (c : JobType K d) (A : Finset (Fin K)) : ℝ :=
  if A = ∅ then 0 else (∑ s ∈ A, rbar ε n s) / (A.card : ℝ) - rr ε n c

/-- `H = 2 Σ_{c,A} k(c,A) g(c,A)` with coefficients frozen at the job-count vector `n` -/
noncomputable def Hf (ε : ℝ) (n : PSState K d) (k : RosState K d) : ℝ :=
  2 * ∑ c, ∑ A, (k c A : ℝ) * gg ε n c A

lemma busy_sum (k : RosState K d) :
    ∑ s, (rosBusy K d k s : ℝ) = ∑ c, ∑ A, (k c A : ℝ) * (A.card : ℝ) := by
  classical
  simp only [rosBusy, Nat.cast_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma inserv_le (k : RosState K d) (hb : ∀ s, rosBusy K d k s ≤ 1) :
    ∑ c, ∑ A, (if A = ∅ then (0 : ℝ) else (k c A : ℝ)) ≤ K := by
  have h1 : ∀ c A, (if A = ∅ then (0 : ℝ) else (k c A : ℝ)) ≤ (k c A : ℝ) * (A.card : ℝ) := by
    intro c A
    split_ifs with hA
    · positivity
    · have : (1 : ℝ) ≤ A.card := by
        exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hA)
      nlinarith [(Nat.cast_nonneg (k c A) : (0 : ℝ) ≤ k c A)]
  calc ∑ c, ∑ A, (if A = ∅ then (0 : ℝ) else (k c A : ℝ))
      ≤ ∑ c, ∑ A, (k c A : ℝ) * (A.card : ℝ) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun A _ => h1 c A
    _ = ∑ s, (rosBusy K d k s : ℝ) := (busy_sum k).symm
    _ ≤ ∑ _s : Fin K, (1 : ℝ) := Finset.sum_le_sum fun s _ => by exact_mod_cast hb s
    _ = K := by simp

lemma gg_ge (ε : ℝ) (n : PSState K d) (c : JobType K d) (A : Finset (Fin K)) :
    (if A = ∅ then (0 : ℝ) else -(d * (Tn n : ℝ))) ≤ gg ε n c A := by
  unfold gg
  split_ifs with hA
  · exact le_rfl
  · have h1 : 0 ≤ (∑ s ∈ A, rbar ε n s) / (A.card : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => rbar_nonneg _ _ _) (Nat.cast_nonneg _)
    linarith [rr_le_Sc ε n c, Sc_le n c]

lemma Hf_ge (ε : ℝ) (n : PSState K d) (k : RosState K d) (hb : ∀ s, rosBusy K d k s ≤ 1) :
    -(2 * (d * (Tn n : ℝ)) * K) ≤ Hf ε n k := by
  have hdT : (0 : ℝ) ≤ d * (Tn n : ℝ) := by positivity
  have h1 : ∀ c A, -(d * (Tn n : ℝ)) * (if A = ∅ then (0 : ℝ) else (k c A : ℝ)) ≤
      (k c A : ℝ) * gg ε n c A := by
    intro c A
    have := gg_ge ε n c A
    have hk : (0 : ℝ) ≤ k c A := Nat.cast_nonneg _
    split_ifs at this ⊢ with hA
    · rw [mul_zero]; nlinarith
    · nlinarith
  have h2 := inserv_le k hb
  unfold Hf
  have h3 : -(d * (Tn n : ℝ)) * ∑ c, ∑ A, (if A = ∅ then (0 : ℝ) else (k c A : ℝ)) ≤
      ∑ c, ∑ A, (k c A : ℝ) * gg ε n c A := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun A _ => h1 c A
  nlinarith

lemma Phi_ge (n : PSState K d) : ((d : ℝ) * Tn n) ^ 2 ≤ K * Phi n := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin K)))
    (f := fun s => (copies K d n s : ℝ))
  rw [sum_copies, Finset.card_univ, Fintype.card_fin, ← Tn_cast] at h
  exact h

/-- the ROS Lyapunov function -/
noncomputable def VV (ε B θ : ℝ) (k : RosState K d) : ℝ :=
  Phi (rosJobs K d k) + Hf ε (rosJobs K d k) k + (K : ℝ) ^ 3 +
    B * (1 - θ ^ Tn (rosJobs K d k))

lemma VV_nonneg (ε B θ : ℝ) (hK : 0 < K) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (k : RosState K d) (hb : ∀ s, rosBusy K d k s ≤ 1) : 0 ≤ VV ε B θ k := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := Phi_ge (rosJobs K d k)
  have h2 := Hf_ge ε (rosJobs K d k) k hb
  have h3 := mul_le_mul_of_nonneg_left h2 hK'.le
  have hp : θ ^ Tn (rosJobs K d k) ≤ 1 := pow_le_one₀ hθ0 hθ1
  have h4 : 0 ≤ B * (1 - θ ^ Tn (rosJobs K d k)) := mul_nonneg hB (by linarith)
  have h5 : 0 ≤ K * (Phi (rosJobs K d k) + Hf ε (rosJobs K d k) k + (K : ℝ) ^ 3) := by
    nlinarith [sq_nonneg ((d : ℝ) * Tn (rosJobs K d k) - (K : ℝ) ^ 2)]
  unfold VV
  have : 0 ≤ Phi (rosJobs K d k) + Hf ε (rosJobs K d k) k + (K : ℝ) ^ 3 :=
    (mul_nonneg_iff_of_pos_left hK').1 h5
  linarith

lemma prod_lip {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hP0 : 0 ≤ ∏ j ∈ s, a j := Finset.prod_nonneg fun j _ => ha0 j
    have hP1 : ∏ j ∈ s, a j ≤ 1 := Finset.prod_le_one (fun j _ => ha0 j) (fun j _ => ha1 j)
    have e : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        (a i - b i) * ∏ j ∈ s, a j + b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) := by ring
    rw [e]
    calc |(a i - b i) * ∏ j ∈ s, a j + b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j)|
        ≤ |(a i - b i) * ∏ j ∈ s, a j| + |b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j)| := abs_add_le _ _
      _ = |a i - b i| * |∏ j ∈ s, a j| + |b i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| := by
          rw [abs_mul, abs_mul]
      _ ≤ |a i - b i| * 1 + 1 * ∑ j ∈ s, |a j - b j| := by
          gcongr
          · rw [abs_of_nonneg hP0]; exact hP1
          · rw [abs_of_nonneg (hb0 i)]; exact hb1 i
      _ = |a i - b i| + ∑ j ∈ s, |a j - b j| := by ring

lemma psi_lip (ε u v : ℝ) (hε : 0 < ε) : |psi ε u - psi ε v| ≤ 2 / ε * |u - v| := by
  unfold psi
  have h1 := abs_min_sub_min_le_max (1 : ℝ) (max 0 ((u - ε / 2) / (ε / 2))) 1
    (max 0 ((v - ε / 2) / (ε / 2)))
  have h2 := abs_max_sub_max_le_max (0 : ℝ) ((u - ε / 2) / (ε / 2)) 0 ((v - ε / 2) / (ε / 2))
  simp only [sub_self, abs_zero] at h1 h2
  have h1' := h1.trans (max_le (abs_nonneg _) le_rfl)
  have h2' := h2.trans (max_le (abs_nonneg _) le_rfl)
  have e : (u - ε / 2) / (ε / 2) - (v - ε / 2) / (ε / 2) = 2 / ε * (u - v) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ε)] at h2'
  exact h1'.trans h2'

lemma frac_step (M M' T : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hMT : M ≤ T) (h1 : M ≤ M')
    (h2 : M' ≤ M + 1) : |M' / (T + 1) - M / T| ≤ 1 / (T + 1) := by
  rcases hT.lt_or_eq with hT | hT
  · have e : M' / (T + 1) - M / T = ((M' - M) * T - M) / (T * (T + 1)) := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < T * (T + 1)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : |(M' - M) * T - M| ≤ T := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    nlinarith
  · subst hT
    have hM0 : M = 0 := le_antisymm hMT hM
    subst hM0
    simp only [div_zero, sub_zero, zero_add, div_one]
    rw [abs_le]; constructor <;> linarith

end ROS50

namespace ROS50

open RedundancyStab.IID Finset PS50

variable {K d : ℕ}

/-- one more type-`c0` job -/
def up (n : PSState K d) (c0 : JobType K d) : PSState K d := Function.update n c0 (n c0 + 1)

lemma upd_cast (n : PSState K d) (c0 c : JobType K d) :
    ((up n c0 c : ℕ) : ℝ) = n c + if c = c0 then 1 else 0 := by
  unfold up
  by_cases h : c = c0
  · subst h; simp
  · simp [h]

lemma copies_succ (n : PSState K d) (c0 : JobType K d) (l : Fin K) :
    (copies K d (up n c0) l : ℝ) = copies K d n l + if l ∈ c0.1 then 1 else 0 := by
  unfold up
  rw [copies_update]; split_ifs <;> push_cast <;> ring

lemma Tn_succ (n : PSState K d) (c0 : JobType K d) : (Tn (up n c0) : ℝ) = Tn n + 1 := by
  unfold up
  have := Tn_update n c0 (n c0 + 1)
  have h : Tn (Function.update n c0 (n c0 + 1)) = Tn n + 1 := by omega
  rw [h]; push_cast; ring

lemma chi_lip (ε : ℝ) (hε : 0 < ε) (n : PSState K d) (c0 c : JobType K d) :
    |chi ε (up n c0) c - chi ε n c| ≤ d * (2 / ε * (1 / ((Tn n : ℝ) + 1))) := by
  unfold chi
  refine (prod_lip c.1 (fun l => psi ε ((copies K d (up n c0) l : ℝ) / (Tn (up n c0) : ℝ)))
    (fun l => psi ε ((copies K d n l : ℝ) / (Tn n : ℝ)))
    (fun _ => psi_nonneg _ _) (fun _ => psi_le_one _ _) (fun _ => psi_nonneg _ _)
    (fun _ => psi_le_one _ _)).trans ?_
  calc ∑ l ∈ c.1, |psi ε ((copies K d (up n c0) l : ℝ) / (Tn (up n c0) : ℝ)) -
        psi ε ((copies K d n l : ℝ) / (Tn n : ℝ))|
      ≤ ∑ _l ∈ c.1, 2 / ε * (1 / ((Tn n : ℝ) + 1)) := Finset.sum_le_sum fun l _ => by
        refine (psi_lip ε _ _ hε).trans ?_
        rw [Tn_succ, copies_succ]
        have hr := frac_step (copies K d n l : ℝ)
          ((copies K d n l : ℝ) + if l ∈ c0.1 then 1 else 0) (Tn n : ℝ) (Nat.cast_nonneg _)
          (Nat.cast_nonneg _) (copies_le_T n l) (by split_ifs <;> linarith)
          (by split_ifs <;> linarith)
        exact mul_le_mul_of_nonneg_left hr (by positivity)
    _ = d * (2 / ε * (1 / ((Tn n : ℝ) + 1))) := by rw [Finset.sum_const, c.2, nsmul_eq_mul]

lemma Sc_succ (n : PSState K d) (c0 c : JobType K d) :
    Sc (up n c0) c = Sc n c + ∑ l ∈ c.1, (if l ∈ c0.1 then (1 : ℝ) else 0) := by
  unfold Sc; simp_rw [copies_succ]; rw [Finset.sum_add_distrib]

lemma rr_lip (ε : ℝ) (hε : 0 < ε) (n : PSState K d) (c0 c : JobType K d) :
    |rr ε (up n c0) c - rr ε n c| ≤ d + 2 * d ^ 2 / ε := by
  have hT : (0 : ℝ) ≤ Tn n := Nat.cast_nonneg _
  have hD0 : 0 ≤ ∑ l ∈ c.1, (if l ∈ c0.1 then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hD1 : ∑ l ∈ c.1, (if l ∈ c0.1 then (1 : ℝ) else 0) ≤ d := by
    calc ∑ l ∈ c.1, (if l ∈ c0.1 then (1 : ℝ) else 0) ≤ ∑ _l ∈ c.1, (1 : ℝ) :=
          Finset.sum_le_sum fun l _ => by split_ifs <;> norm_num
      _ = d := by rw [Finset.sum_const, c.2]; simp
  have hχ := chi_lip ε hε n c0 c
  have hS := Sc_le n c
  have hS0 := Sc_nonneg n c
  have e : rr ε (up n c0) c - rr ε n c =
      (∑ l ∈ c.1, (if l ∈ c0.1 then (1 : ℝ) else 0)) * chi ε (up n c0) c +
        Sc n c * (chi ε (up n c0) c - chi ε n c) := by
    unfold rr; rw [Sc_succ]; ring
  rw [e]
  have h1 : |(∑ l ∈ c.1, (if l ∈ c0.1 then (1 : ℝ) else 0)) * chi ε (up n c0) c| ≤ d := by
    rw [abs_mul, abs_of_nonneg hD0, abs_of_nonneg (chi_nonneg _ _ _)]
    nlinarith [chi_le_one ε (up n c0) c, chi_nonneg ε (up n c0) c]
  have h2 : |Sc n c * (chi ε (up n c0) c - chi ε n c)| ≤ 2 * d ^ 2 / ε := by
    rw [abs_mul, abs_of_nonneg hS0]
    have hq : Sc n c * (1 / ((Tn n : ℝ) + 1)) ≤ d := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    calc Sc n c * |chi ε (up n c0) c - chi ε n c|
        ≤ Sc n c * (d * (2 / ε * (1 / ((Tn n : ℝ) + 1)))) := mul_le_mul_of_nonneg_left hχ hS0
      _ = (Sc n c * (1 / ((Tn n : ℝ) + 1))) * (d * (2 / ε)) := by ring
      _ ≤ d * (d * (2 / ε)) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = 2 * d ^ 2 / ε := by ring
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

lemma rbar_lip (ε : ℝ) (hε : 0 < ε) (n : PSState K d) (c0 : JobType K d) (s : Fin K) :
    |rbar ε (up n c0) s - rbar ε n s| ≤ (d + 2 * d ^ 2 / ε) + 2 * d / ε := by
  have hsplit : rbar ε (up n c0) s - rbar ε n s =
      ∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) *
        (rr ε (up n c0) c - rr ε n c) +
      (∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) * rr ε n c -
        rbar ε n s) := by
    unfold rbar; simp only [mul_sub, Finset.sum_sub_distrib]; ring
  have hfirst : |∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) *
      (rr ε (up n c0) c - rr ε n c)| ≤ d + 2 * d ^ 2 / ε := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ c ∈ typesAt K d s, |(up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) *
          (rr ε (up n c0) c - rr ε n c)|
        ≤ ∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) *
          (d + 2 * d ^ 2 / ε) := Finset.sum_le_sum fun c _ => by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (rr_lip ε hε n c0 c) (by positivity)
      _ = (∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ)) *
          (d + 2 * d ^ 2 / ε) := by rw [Finset.sum_mul]
      _ ≤ 1 * (d + 2 * d ^ 2 / ε) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [busy_eq]; split_ifs <;> norm_num
      _ = d + 2 * d ^ 2 / ε := one_mul _
  have hsecond : |∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) *
      rr ε n c - rbar ε n s| ≤ 2 * d / ε := by
    have hR : rbar ε n s = (∑ c ∈ typesAt K d s, (n c : ℝ) * rr ε n c) /
        (copies K d n s : ℝ) := by
      unfold rbar; rw [Finset.sum_div]; exact Finset.sum_congr rfl fun c _ => by ring
    have hR0 := rbar_nonneg ε n s
    have hRle := rbar_le ε hε n s
    have hFM : (∑ c ∈ typesAt K d s, (n c : ℝ) * rr ε n c) =
        (copies K d n s : ℝ) * rbar ε n s := by
      by_cases hM : (copies K d n s : ℝ) = 0
      · rw [hM, zero_mul]
        refine Finset.sum_eq_zero fun c hc => ?_
        have h1 := le_copies n c s (mem_of_typesAt hc)
        have h2 : copies K d n s = 0 := by exact_mod_cast hM
        have hn : n c = 0 := by omega
        simp [hn]
      · rw [hR]; field_simp
    by_cases hs : s ∈ c0.1
    · have hM' : (copies K d (up n c0) s : ℝ) = copies K d n s + 1 := by
        rw [copies_succ, if_pos hs]
      have hc0 : c0 ∈ typesAt K d s := by simp [typesAt, hs]
      have hsum : ∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) *
          rr ε n c = ((copies K d n s : ℝ) * rbar ε n s + rr ε n c0) /
            ((copies K d n s : ℝ) + 1) := by
        rw [hM', ← hFM]
        calc ∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / ((copies K d n s : ℝ) + 1) * rr ε n c
            = (∑ c ∈ typesAt K d s, (up n c0 c : ℝ) * rr ε n c) /
                ((copies K d n s : ℝ) + 1) := by
              rw [Finset.sum_div]; exact Finset.sum_congr rfl fun c _ => by ring
          _ = _ := by
              congr 1
              simp_rw [upd_cast, add_mul, Finset.sum_add_distrib]
              congr 1
              simp [ite_mul, hc0]
      have hr0 := rr_nonneg ε n c0
      have hr0le := rr_le_M ε hε n c0 s hs
      have hM0 : (0 : ℝ) ≤ copies K d n s := Nat.cast_nonneg _
      rw [hsum]
      have e : ((copies K d n s : ℝ) * rbar ε n s + rr ε n c0) / ((copies K d n s : ℝ) + 1) -
          rbar ε n s = (rr ε n c0 - rbar ε n s) / ((copies K d n s : ℝ) + 1) := by
        field_simp; ring
      rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (copies K d n s : ℝ) + 1),
        div_le_iff₀ (by positivity)]
      have b1 : rr ε n c0 ≤ 2 * d / ε * ((copies K d n s : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
      have b2 : rbar ε n s ≤ 2 * d / ε * ((copies K d n s : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · have hM' : (copies K d (up n c0) s : ℝ) = copies K d n s := by
        rw [copies_succ, if_neg hs, add_zero]
      have : ∑ c ∈ typesAt K d s, (up n c0 c : ℝ) / (copies K d (up n c0) s : ℝ) *
          rr ε n c = rbar ε n s := by
        unfold rbar; rw [hM']
        refine Finset.sum_congr rfl fun c hc => ?_
        have hcc : c ≠ c0 := fun h => hs (h ▸ mem_of_typesAt hc)
        rw [upd_cast, if_neg hcc, add_zero]
      rw [this, sub_self, abs_zero]; positivity
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

lemma gg_lip (ε : ℝ) (hε : 0 < ε) (n : PSState K d) (c0 c : JobType K d) (A : Finset (Fin K)) :
    |gg ε (up n c0) c A - gg ε n c A| ≤
      (if A = ∅ then 0 else ((d + 2 * d ^ 2 / ε) + 2 * d / ε) + (d + 2 * d ^ 2 / ε)) := by
  unfold gg
  split_ifs with hA
  · simp
  · have hcard : (0 : ℝ) < A.card := by
      exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hA)
    have e : (∑ s ∈ A, rbar ε (up n c0) s) / (A.card : ℝ) - rr ε (up n c0) c -
        ((∑ s ∈ A, rbar ε n s) / (A.card : ℝ) - rr ε n c) =
        (∑ s ∈ A, (rbar ε (up n c0) s - rbar ε n s)) / (A.card : ℝ) -
          (rr ε (up n c0) c - rr ε n c) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [e]
    have h1 : |(∑ s ∈ A, (rbar ε (up n c0) s - rbar ε n s)) / (A.card : ℝ)| ≤
        (d + 2 * d ^ 2 / ε) + 2 * d / ε := by
      rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
      calc |∑ s ∈ A, (rbar ε (up n c0) s - rbar ε n s)|
          ≤ ∑ s ∈ A, |rbar ε (up n c0) s - rbar ε n s| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _s ∈ A, ((d + 2 * d ^ 2 / ε) + 2 * d / ε) :=
            Finset.sum_le_sum fun s _ => rbar_lip ε hε n c0 s
        _ = ((d + 2 * d ^ 2 / ε) + 2 * d / ε) * A.card := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact (abs_sub _ _).trans (add_le_add h1 (rr_lip ε hε n c0 c))

lemma Hf_coef (ε : ℝ) (hε : 0 < ε) (n : PSState K d) (c0 : JobType K d) (k : RosState K d)
    (hb : ∀ s, rosBusy K d k s ≤ 1) :
    |Hf ε (up n c0) k - Hf ε n k| ≤
      2 * K * (((d + 2 * d ^ 2 / ε) + 2 * d / ε) + (d + 2 * d ^ 2 / ε)) := by
  have hC : (0 : ℝ) ≤ ((d + 2 * d ^ 2 / ε) + 2 * d / ε) + (d + 2 * d ^ 2 / ε) := by positivity
  have e : Hf ε (up n c0) k - Hf ε n k =
      2 * ∑ c, ∑ A, (k c A : ℝ) * (gg ε (up n c0) c A - gg ε n c A) := by
    unfold Hf; simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e, abs_mul, abs_two]
  have h1 : ∀ c A, |(k c A : ℝ) * (gg ε (up n c0) c A - gg ε n c A)| ≤
      (if A = ∅ then (0 : ℝ) else (k c A : ℝ)) *
        (((d + 2 * d ^ 2 / ε) + 2 * d / ε) + (d + 2 * d ^ 2 / ε)) := by
    intro c A
    rw [abs_mul, Nat.abs_cast]
    have := gg_lip ε hε n c0 c A
    split_ifs at this ⊢ with hA
    · rw [zero_mul]; nlinarith [abs_nonneg (gg ε (up n c0) c A - gg ε n c A),
        (Nat.cast_nonneg (k c A) : (0 : ℝ) ≤ k c A)]
    · exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have h2 : |∑ c, ∑ A, (k c A : ℝ) * (gg ε (up n c0) c A - gg ε n c A)| ≤
      (∑ c, ∑ A, (if A = ∅ then (0 : ℝ) else (k c A : ℝ))) *
        (((d + 2 * d ^ 2 / ε) + 2 * d / ε) + (d + 2 * d ^ 2 / ε)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun A _ => h1 c A
  have h3 := mul_le_mul_of_nonneg_right (inserv_le k hb) hC
  nlinarith

end ROS50

namespace ROS50

open RedundancyStab.IID Finset PS50

variable {K d : ℕ}

/-- real waiting weights of the ROS pick at `s` -/
noncomputable def wr (k : RosState K d) (s : Fin K) (p : JobType K d × Finset (Fin K)) : ℝ :=
  if s ∈ p.1.1 ∧ s ∉ p.2 then (k p.1 p.2 : ℝ) else 0

lemma wr_nonneg (k : RosState K d) (s : Fin K) (p : JobType K d × Finset (Fin K)) :
    0 ≤ wr k s p := by unfold wr; split_ifs <;> positivity

lemma ww_eq (k : RosState K d) (s : Fin K) (p : JobType K d × Finset (Fin K)) :
    rosWaitWeight K d k s p = ENNReal.ofReal (wr k s p) := by
  unfold rosWaitWeight wr; split_ifs <;> simp

lemma map_tsum {ι Y : Type*} [Fintype ι] (p : PMF ι) (g : ι → Y) (V : Y → ℝ≥0∞) :
    ∑' z, (p.map g) z * V z = ∑ i, p i * V (g i) := bind_pure_tsum p g V

lemma pick_exp (k : RosState K d) (s : Fin K) (f : RosState K d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfk : 0 ≤ f k)
    (hf : ∀ c A, s ∈ c.1 → s ∉ A → 1 ≤ k c A → 0 ≤ f (rosStartAt K d k s c A))
    (hbound : ∑ p, wr k s p * f (rosStartAt K d k s p.1 p.2) ≤ (f k + C) * ∑ p, wr k s p) :
    ∑' z, rosPick K d k s z * ENNReal.ofReal (f z) ≤ ENNReal.ofReal (f k + C) := by
  classical
  have hsum : ∑ p, rosWaitWeight K d k s p = ENNReal.ofReal (∑ p, wr k s p) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => wr_nonneg k s p)]
    simp_rw [ww_eq]
  have hnn : ∀ p ∈ (univ : Finset (JobType K d × Finset (Fin K))),
      0 ≤ wr k s p * f (rosStartAt K d k s p.1 p.2) := by
    intro p _
    unfold wr
    split_ifs with hp
    · by_cases hk0 : k p.1 p.2 = 0
      · simp [hk0]
      · exact mul_nonneg (Nat.cast_nonneg _) (hf p.1 p.2 hp.1 hp.2 (Nat.one_le_iff_ne_zero.2 hk0))
    · simp
  unfold rosPick
  split_ifs with h
  · rw [map_tsum]
    simp_rw [PMF.normalize_apply]
    rw [tsum_fintype, hsum]
    have hS0 : 0 < ∑ p, wr k s p := by
      by_contra hc; push Not at hc
      apply h.1; rw [hsum]; exact ENNReal.ofReal_eq_zero.2 hc
    calc ∑ p, rosWaitWeight K d k s p * (ENNReal.ofReal (∑ p, wr k s p))⁻¹ *
          ENNReal.ofReal (f (rosStartAt K d k s p.1 p.2))
        = ENNReal.ofReal (∑ p, wr k s p * f (rosStartAt K d k s p.1 p.2)) *
            (ENNReal.ofReal (∑ p, wr k s p))⁻¹ := by
          rw [ENNReal.ofReal_sum_of_nonneg hnn, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [ww_eq, ENNReal.ofReal_mul (wr_nonneg k s p)]
          ring
      _ = ENNReal.ofReal ((∑ p, wr k s p * f (rosStartAt K d k s p.1 p.2)) /
            ∑ p, wr k s p) := by
          rw [ENNReal.ofReal_div_of_pos hS0, div_eq_mul_inv]
      _ ≤ ENNReal.ofReal (f k + C) :=
          ENNReal.ofReal_le_ofReal (by rw [div_le_iff₀ hS0]; exact hbound)
  · rw [tsum_eq_single k]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · intro z hz; simp [PMF.pure_apply, hz]

lemma start_cast (k : RosState K d) (s : Fin K) (c : JobType K d) (A : Finset (Fin K))
    (hk : 1 ≤ k c A) (c' : JobType K d) (A' : Finset (Fin K)) :
    ((rosStartAt K d k s c A c' A' : ℕ) : ℝ) = k c' A' - (if c' = c ∧ A' = A then 1 else 0) +
      (if c' = c ∧ A' = insert s A then 1 else 0) := by
  unfold rosStartAt
  rw [add_apply]
  have h := congrArg (Nat.cast : ℕ → ℝ) (remove_apply k c A hk c' A')
  push_cast at h ⊢
  linarith

lemma delta_sum (f : JobType K d → Finset (Fin K) → ℝ) (c : JobType K d) (B : Finset (Fin K)) :
    ∑ c', ∑ A', (if c' = c ∧ A' = B then (1 : ℝ) else 0) * f c' A' = f c B := by
  simp [ite_and]

lemma Hf_start (ε : ℝ) (n : PSState K d) (k : RosState K d) (s : Fin K) (c : JobType K d)
    (A : Finset (Fin K)) (hk : 1 ≤ k c A) :
    Hf ε n (rosStartAt K d k s c A) = Hf ε n k + 2 * (gg ε n c (insert s A) - gg ε n c A) := by
  unfold Hf
  simp_rw [start_cast k s c A hk]
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [delta_sum (fun c' A' => gg ε n c' A'), delta_sum (fun c' A' => gg ε n c' A')]
  ring

lemma gg_insert (ε : ℝ) (n : PSState K d) (c : JobType K d) (s : Fin K) (A : Finset (Fin K))
    (hsA : s ∉ A) :
    gg ε n c (insert s A) - gg ε n c A ≤ rbar ε n s - (if A = ∅ then rr ε n c else 0) := by
  unfold gg
  rw [if_neg (Finset.insert_ne_empty s A), Finset.sum_insert hsA, Finset.card_insert_eq_ite,
    if_neg hsA]
  split_ifs with hA
  · subst hA; simp
  · have ha : (1 : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hA)
    have hX : 0 ≤ ∑ x ∈ A, rbar ε n x := Finset.sum_nonneg fun _ _ => rbar_nonneg _ _ _
    have hr := rbar_nonneg ε n s
    push_cast
    have h1 : rbar ε n s / ((A.card : ℝ) + 1) ≤ rbar ε n s := div_le_self hr (by linarith)
    have h2 : (∑ x ∈ A, rbar ε n x) / ((A.card : ℝ) + 1) ≤ (∑ x ∈ A, rbar ε n x) / A.card :=
      div_le_div_of_nonneg_left hX (by linarith) (by linarith)
    rw [add_div]
    linarith

lemma jobs_split (k : RosState K d) (c : JobType K d) :
    (rosJobs K d k c : ℝ) = k c ∅ + ∑ A, (if A = ∅ then (0 : ℝ) else k c A) := by
  unfold rosJobs; push_cast
  rw [← Finset.add_sum_erase _ _ (mem_univ (∅ : Finset (Fin K))),
    ← Finset.add_sum_erase _ (fun A => if A = ∅ then (0 : ℝ) else k c A)
      (mem_univ (∅ : Finset (Fin K))), if_pos rfl, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun A hA => by rw [if_neg (Finset.ne_of_mem_erase hA)]

lemma rbar_mul (ε : ℝ) (n : PSState K d) (s : Fin K) :
    (copies K d n s : ℝ) * rbar ε n s = ∑ c ∈ typesAt K d s, (n c : ℝ) * rr ε n c := by
  by_cases hM : (copies K d n s : ℝ) = 0
  · rw [hM, zero_mul]
    symm
    refine Finset.sum_eq_zero fun c hc => ?_
    have h1 := le_copies n c s (mem_of_typesAt hc)
    have h2 : copies K d n s = 0 := by exact_mod_cast hM
    have hn : n c = 0 := by omega
    simp [hn]
  · unfold rbar
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by field_simp

lemma wr_sum (k : RosState K d) (s : Fin K) (hs0 : rosBusy K d k s = 0) :
    ∑ p, wr k s p = (copies K d (rosJobs K d k) s : ℝ) := by
  classical
  have hz : ∀ c A, s ∈ A → k c A = 0 := fun c A h => zero_of_busy_zero k s hs0 c A h
  rw [Fintype.sum_prod_type, copies_cast]
  simp only [typesAt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold wr rosJobs
  split_ifs with hc
  · push_cast
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : s ∈ A
    · simp [hA, hz c A hA]
    · simp [hc, hA]
  · simp [hc]

lemma pick_real (ε : ℝ) (hε : 0 < ε) (k : RosState K d) (s : Fin K) (hs0 : rosBusy K d k s = 0)
    (hb : ∀ s, rosBusy K d k s ≤ 1) :
    ∑ p, wr k s p * (gg ε (rosJobs K d k) p.1 (insert s p.2) - gg ε (rosJobs K d k) p.1 p.2) ≤
      2 * d * K / ε * (copies K d (rosJobs K d k) s : ℝ) := by
  classical
  have hM0 : (0 : ℝ) ≤ copies K d (rosJobs K d k) s := Nat.cast_nonneg _
  have step1 : ∑ p, wr k s p * (gg ε (rosJobs K d k) p.1 (insert s p.2) -
      gg ε (rosJobs K d k) p.1 p.2) ≤ ∑ p, wr k s p * (rbar ε (rosJobs K d k) s -
        (if p.2 = ∅ then rr ε (rosJobs K d k) p.1 else 0)) := by
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : s ∈ p.1.1 ∧ s ∉ p.2
    · exact mul_le_mul_of_nonneg_left (gg_insert ε _ p.1 s p.2 hp.2) (wr_nonneg k s p)
    · simp [wr, hp]
  have e2 : ∑ p, wr k s p * (rbar ε (rosJobs K d k) s -
        (if p.2 = ∅ then rr ε (rosJobs K d k) p.1 else 0)) =
      rbar ε (rosJobs K d k) s * (copies K d (rosJobs K d k) s : ℝ) -
        ∑ c ∈ typesAt K d s, (k c ∅ : ℝ) * rr ε (rosJobs K d k) c := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, wr_sum k s hs0, mul_comm]
    congr 1
    rw [Fintype.sum_prod_type]
    simp only [typesAt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single (∅ : Finset (Fin K))]
    · unfold wr; simp
    · intro A _ hA; simp [hA]
    · intro h; exact absurd (mem_univ _) h
  have e3 : rbar ε (rosJobs K d k) s * (copies K d (rosJobs K d k) s : ℝ) -
      ∑ c ∈ typesAt K d s, (k c ∅ : ℝ) * rr ε (rosJobs K d k) c =
      ∑ c ∈ typesAt K d s, (∑ A, (if A = ∅ then (0 : ℝ) else k c A)) *
        rr ε (rosJobs K d k) c := by
    rw [mul_comm, rbar_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [jobs_split]; ring
  have hbnd : ∀ c ∈ typesAt K d s, (∑ A, (if A = ∅ then (0 : ℝ) else k c A)) *
      rr ε (rosJobs K d k) c ≤
      (∑ A, (if A = ∅ then (0 : ℝ) else k c A)) * (2 * d / ε * (copies K d (rosJobs K d k) s : ℝ)) := by
    intro c hc
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun A _ => by split_ifs <;> positivity)
    have := rr_le_M ε hε (rosJobs K d k) c s (mem_of_typesAt hc)
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]; linarith
  have h4 : ∑ c ∈ typesAt K d s, (∑ A, (if A = ∅ then (0 : ℝ) else k c A)) *
      (2 * d / ε * (copies K d (rosJobs K d k) s : ℝ)) ≤
      (∑ c, ∑ A, (if A = ∅ then (0 : ℝ) else k c A)) *
        (2 * d / ε * (copies K d (rosJobs K d k) s : ℝ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ =>
      mul_nonneg (Finset.sum_nonneg fun A _ => by split_ifs <;> positivity) (by positivity)
  have h5 := mul_le_mul_of_nonneg_right (inserv_le k hb)
    (by positivity : (0 : ℝ) ≤ 2 * d / ε * (copies K d (rosJobs K d k) s : ℝ))
  have e6 : (K : ℝ) * (2 * d / ε * (copies K d (rosJobs K d k) s : ℝ)) =
      2 * d * K / ε * (copies K d (rosJobs K d k) s : ℝ) := by ring
  rw [e2, e3] at step1
  linarith [Finset.sum_le_sum hbnd]

lemma jobs_start' (k : RosState K d) (s : Fin K) (c : JobType K d) (A : Finset (Fin K))
    (h : 1 ≤ k c A) : rosJobs K d (rosStartAt K d k s c A) = rosJobs K d k :=
  funext fun c' => jobs_start k s c A h c'

lemma VV_start (ε B θ : ℝ) (k : RosState K d) (s : Fin K) (c : JobType K d) (A : Finset (Fin K))
    (h : 1 ≤ k c A) : VV ε B θ (rosStartAt K d k s c A) = VV ε B θ k +
      2 * (gg ε (rosJobs K d k) c (insert s A) - gg ε (rosJobs K d k) c A) := by
  unfold VV
  rw [jobs_start' k s c A h, Hf_start ε _ k s c A h]
  ring

lemma pick_VV (ε B θ a : ℝ) (hε : 0 < ε) (hK : 0 < K) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (k : RosState K d) (s : Fin K) (hs0 : rosBusy K d k s = 0)
    (hb : ∀ s, rosBusy K d k s ≤ 1) :
    ∑' z, rosPick K d k s z * ENNReal.ofReal (VV ε B θ z + a) ≤
      ENNReal.ofReal (VV ε B θ k + a + 4 * d * K / ε) := by
  refine pick_exp k s (fun z => VV ε B θ z + a) (4 * d * K / ε) (by positivity)
    (by linarith [VV_nonneg ε B θ hK hB hθ0 hθ1 k hb]) ?_ ?_
  · intro c A hsc hsA h1
    have hb' : ∀ s', rosBusy K d (rosStartAt K d k s c A) s' ≤ 1 := by
      intro s'
      rw [busy_start k s c A hsA h1 s']
      split_ifs with hs'
      · subst hs'; omega
      · simpa using hb s'
    linarith [VV_nonneg ε B θ hK hB hθ0 hθ1 _ hb']
  · have e : ∀ p : JobType K d × Finset (Fin K),
        wr k s p * (VV ε B θ (rosStartAt K d k s p.1 p.2) + a) =
        wr k s p * (VV ε B θ k + a) + 2 * (wr k s p *
          (gg ε (rosJobs K d k) p.1 (insert s p.2) - gg ε (rosJobs K d k) p.1 p.2)) := by
      intro p
      by_cases hp : s ∈ p.1.1 ∧ s ∉ p.2 ∧ k p.1 p.2 ≠ 0
      · rw [VV_start ε B θ k s p.1 p.2 (Nat.one_le_iff_ne_zero.2 hp.2.2)]; ring
      · have : wr k s p = 0 := by
          unfold wr
          split_ifs with hq
          · have : k p.1 p.2 = 0 := by by_contra hne; exact hp ⟨hq.1, hq.2, hne⟩
            simp [this]
          · rfl
        rw [this]; ring
    try beta_reduce
    rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, wr_sum k s hs0]
    have := pick_real ε hε k s hs0 hb
    have hM0 : (0 : ℝ) ≤ copies K d (rosJobs K d k) s := Nat.cast_nonneg _
    have e2 : (VV ε B θ k + a + 4 * d * K / ε) * (copies K d (rosJobs K d k) s : ℝ) =
        (VV ε B θ k + a) * (copies K d (rosJobs K d k) s : ℝ) +
          2 * (2 * d * K / ε * (copies K d (rosJobs K d k) s : ℝ)) := by ring
    rw [e2]
    linarith

lemma refill_VV (ε B θ : ℝ) (hε : 0 < ε) (hK : 0 < K) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : ∀ (l : List (Fin K)), l.Nodup → ∀ (k : RosState K d), InvL l.toFinset k →
    ∀ a : ℝ, 0 ≤ a →
    ∑' z, rosRefill K d l k z * ENNReal.ofReal (VV ε B θ z + a) ≤
      ENNReal.ofReal (VV ε B θ k + a + l.length * (4 * d * K / ε)) := by
  intro l
  induction l with
  | nil =>
    intro _ k _ a _
    simp only [rosRefill, List.length_nil, Nat.cast_zero, zero_mul, add_zero]
    rw [tsum_eq_single k]
    · simp
    · intro z hz; simp [PMF.pure_apply, hz]
  | cons s l ih =>
    intro hnd k hk a ha
    rw [List.nodup_cons] at hnd
    have hsL : s ∈ (s :: l).toFinset := by simp
    have herase : ((s :: l).toFinset).erase s = l.toFinset := by
      rw [List.toFinset_cons, Finset.erase_insert (by simpa using hnd.1)]
    have hC : (0 : ℝ) ≤ l.length * (4 * d * K / ε) := by positivity
    simp only [rosRefill]
    rw [bind_tsum']
    calc ∑' y, rosPick K d k s y * ∑' z, rosRefill K d l y z * ENNReal.ofReal (VV ε B θ z + a)
        ≤ ∑' y, rosPick K d k s y *
            ENNReal.ofReal (VV ε B θ y + (a + l.length * (4 * d * K / ε))) := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          by_cases hy : rosPick K d k s y = 0
          · rw [hy, zero_mul, zero_mul]
          · gcongr
            have hinv : InvL l.toFinset y := by
              rcases pick_support k s y hy with ⟨rfl, hw⟩ | ⟨c, A, hsc, hsA, h1, rfl⟩
              · have := inv_stay _ y hk s hsL hw
                rwa [herase] at this
              · have := inv_start _ k hk s hsL c A hsc hsA h1
                rwa [herase] at this
            refine (ih hnd.2 y hinv a ha).trans (le_of_eq ?_)
            congr 1; ring
      _ ≤ ENNReal.ofReal (VV ε B θ k + (a + l.length * (4 * d * K / ε)) + 4 * d * K / ε) :=
          pick_VV ε B θ _ hε hK hB hθ0 hθ1 (by positivity) k s (hk.2.2.2 s hsL) hk.2.1
      _ = ENNReal.ofReal (VV ε B θ k + a + (s :: l).length * (4 * d * K / ε)) := by
          congr 1; simp only [List.length_cons]; push_cast; ring

end ROS50

namespace ROS50

open RedundancyStab.IID Finset PS50

variable {K d : ℕ}

lemma Tn_up_nat (n : PSState K d) (c : JobType K d) : Tn (up n c) = Tn n + 1 := by
  unfold up; have := Tn_update n c (n c + 1); omega

lemma Tn_down_nat (n : PSState K d) (c : JobType K d) (hc : 1 ≤ n c) :
    Tn (Function.update n c (n c - 1)) + 1 = Tn n := by
  have := Tn_update n c (n c - 1); omega

lemma up_down (n : PSState K d) (c : JobType K d) (hc : 1 ≤ n c) :
    up (Function.update n c (n c - 1)) c = n := by
  unfold up
  rw [Function.update_self, Function.update_idem, Nat.sub_add_cancel hc, Function.update_eq_self]

lemma jobs_arrive (y : RosState K d) (c : JobType K d) :
    rosJobs K d (rosArrive K d y c) = up (rosJobs K d y) c := by
  funext c'
  unfold rosArrive up
  rw [jobs_add]
  by_cases h : c' = c
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [h]

lemma jobs_rem (y : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (hk : 1 ≤ y c A) :
    rosJobs K d (rosRemove K d y c A) =
      Function.update (rosJobs K d y) c (rosJobs K d y c - 1) := by
  funext c'
  have := jobs_remove y c A hk c'
  by_cases h : c' = c
  · subst h; rw [Function.update_self]; simp at this; omega
  · rw [Function.update_of_ne h]; simpa [h] using this

lemma jobs_pos (y : RosState K d) (c : JobType K d) (A : Finset (Fin K)) (hk : 1 ≤ y c A) :
    1 ≤ rosJobs K d y c := by
  unfold rosJobs
  exact le_trans hk (Finset.single_le_sum (f := fun A => y c A) (fun _ _ => Nat.zero_le _)
    (mem_univ A))

lemma copies_idle (y : RosState K d) (hy : InvL ∅ y) (s : Fin K) (hs : rosBusy K d y s = 0) :
    copies K d (rosJobs K d y) s = 0 := by
  unfold copies
  exact Finset.sum_eq_zero fun c hc => hy.2.2.1 s (by simp) hs c hc

lemma rbar_idle (ε : ℝ) (hε : 0 < ε) (y : RosState K d) (hy : InvL ∅ y) (s : Fin K)
    (hs : rosBusy K d y s = 0) : rbar ε (rosJobs K d y) s = 0 := by
  have h1 := rbar_le ε hε (rosJobs K d y) s
  rw [copies_idle y hy s hs] at h1
  push_cast at h1
  have h2 := rbar_nonneg ε (rosJobs K d y) s
  refine le_antisymm ?_ h2
  nlinarith

lemma Hf_add (ε : ℝ) (n : PSState K d) (k : RosState K d) (c : JobType K d)
    (A : Finset (Fin K)) : Hf ε n (rosAdd K d k c A) = Hf ε n k + 2 * gg ε n c A := by
  unfold Hf
  simp_rw [add_apply]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  rw [delta_sum (fun c' A' => gg ε n c' A')]
  ring

lemma Hf_remove (ε : ℝ) (n : PSState K d) (k : RosState K d) (c : JobType K d)
    (A : Finset (Fin K)) (hk : 1 ≤ k c A) :
    Hf ε n (rosRemove K d k c A) = Hf ε n k - 2 * gg ε n c A := by
  have hc : ∀ c' A', ((rosRemove K d k c A c' A' : ℕ) : ℝ) =
      k c' A' - (if c' = c ∧ A' = A then 1 else 0) := by
    intro c' A'
    have h := congrArg (Nat.cast : ℕ → ℝ) (remove_apply k c A hk c' A')
    push_cast at h
    linarith
  unfold Hf
  simp_rw [hc]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [delta_sum (fun c' A' => gg ε n c' A')]
  ring

lemma phi_down (n : PSState K d) (c : JobType K d) (hc : 1 ≤ n c) :
    Phi (Function.update n c (n c - 1)) = Phi n - 2 * Sc n c + d := by
  rw [phi_update]
  have e : ((n c - 1 : ℕ) : ℝ) - n c = -1 := by rw [Nat.cast_sub hc]; push_cast; ring
  rw [e]
  unfold Sc
  simp only [Finset.sum_add_distrib, Finset.sum_const, c.2, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma gg_arr (ε : ℝ) (hε : 0 < ε) (y : RosState K d) (hy : InvL ∅ y) (c : JobType K d) :
    gg ε (rosJobs K d y) c (c.1.filter (fun s => rosBusy K d y s = 0)) ≤ 0 := by
  unfold gg
  split_ifs
  · exact le_rfl
  · rw [Finset.sum_eq_zero (fun s hs => rbar_idle ε hε y hy s (Finset.mem_filter.1 hs).2),
      zero_div]
    linarith [rr_nonneg ε (rosJobs K d y) c]

/-- constant of the coefficient change -/
noncomputable def Cg (ε : ℝ) (d : ℕ) : ℝ :=
  ((d + 2 * d ^ 2 / ε) + 2 * d / ε) + (d + 2 * d ^ 2 / ε)

lemma VV_arr (ε B θ : ℝ) (hε : 0 < ε) (y : RosState K d) (hy : InvL ∅ y) (c : JobType K d)
    (t : ℕ) (ht : Tn (rosJobs K d y) = t + 1) :
    VV ε B θ (rosArrive K d y c) - VV ε B θ y ≤
      (Phi (up (rosJobs K d y) c) - Phi (rosJobs K d y)) + 2 * K * Cg ε d +
        B * (θ ^ (t + 1) - θ ^ (t + 2)) := by
  have hb' := (inv_arrive y hy c).2.1
  have h1 := (abs_le.1 (Hf_coef ε hε (rosJobs K d y) c (rosArrive K d y c) hb')).2
  have h2 : Hf ε (rosJobs K d y) (rosArrive K d y c) = Hf ε (rosJobs K d y) y +
      2 * gg ε (rosJobs K d y) c (c.1.filter (fun s => rosBusy K d y s = 0)) := by
    unfold rosArrive; exact Hf_add ε _ y c _
  have h3 := gg_arr ε hε y hy c
  have hT : Tn (up (rosJobs K d y) c) = t + 2 := by rw [Tn_up_nat, ht]
  unfold VV
  rw [jobs_arrive, hT, ht]
  unfold Cg
  linarith

lemma VV_dep (ε B θ : ℝ) (hε : 0 < ε) (y : RosState K d) (hy : InvL ∅ y) (c : JobType K d)
    (A : Finset (Fin K)) (hk : 1 ≤ y c A) (t : ℕ) (ht : Tn (rosJobs K d y) = t + 1) :
    VV ε B θ (rosRemove K d y c A) - VV ε B θ y ≤
      -(2 * Sc (rosJobs K d y) c) + d - 2 * gg ε (rosJobs K d y) c A + 2 * K * Cg ε d +
        B * (θ ^ (t + 1) - θ ^ t) := by
  have hj := jobs_pos y c A hk
  have hb1 := (inv_remove y hy c A hk).2.1
  have h1 := (abs_le.1 (Hf_coef ε hε (Function.update (rosJobs K d y) c (rosJobs K d y c - 1)) c
    (rosRemove K d y c A) hb1)).1
  rw [up_down _ c hj] at h1
  have h2 := Hf_remove ε (rosJobs K d y) y c A hk
  have h3 := phi_down (rosJobs K d y) c hj
  have hT : Tn (Function.update (rosJobs K d y) c (rosJobs K d y c - 1)) = t := by
    have := Tn_down_nat (rosJobs K d y) c hj; omega
  unfold VV
  rw [jobs_rem y c A hk, hT, ht, h3]
  unfold Cg
  linarith

lemma arr_total (hd : 1 ≤ d) (hdK : d ≤ K) (lam : ℝ) (n : PSState K d) :
    ∑ c : JobType K d, lam / (K.choose d : ℝ) * (Phi (up n c) - Phi n) =
      lam * d + 2 * lam * d ^ 2 / K * (Tn n : ℝ) := by
  unfold up
  rw [← Finset.mul_sum, arr_phi n hd, ← Tn_cast]
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hC : (K.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdK).ne'
  have hX : ((K - 1).choose (d - 1) : ℝ) = (K.choose d : ℝ) * d / K := by
    rw [eq_div_iff hK, choose_rel hd hdK]
  rw [hX]; field_simp; ring

lemma swap3 (g : JobType K d → Finset (Fin K) → Fin K → ℝ) :
    ∑ s, ∑ c, ∑ A, g c A s = ∑ c, ∑ A, ∑ s, g c A s := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

lemma busy_weighted (y : RosState K d) (f : Fin K → ℝ) :
    ∑ s, (rosBusy K d y s : ℝ) * f s = ∑ c, ∑ A, (y c A : ℝ) * ∑ s ∈ A, f s := by
  classical
  simp only [rosBusy, Nat.cast_sum, Finset.sum_filter, Finset.sum_mul, Nat.cast_ite,
    Nat.cast_zero, ite_mul, zero_mul]
  rw [swap3]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

lemma dep_key (ε : ℝ) (hε : 0 < ε) (y : RosState K d) (hy : InvL ∅ y) :
    ∑ s, rbar ε (rosJobs K d y) s ≤
      ∑ c, ∑ A, (y c A : ℝ) * A.card * (Sc (rosJobs K d y) c + gg ε (rosJobs K d y) c A) := by
  have ha : ∀ c A, (y c A : ℝ) * ∑ s ∈ A, rbar ε (rosJobs K d y) s ≤
      (y c A : ℝ) * A.card * (Sc (rosJobs K d y) c + gg ε (rosJobs K d y) c A) := by
    intro c A
    have hy0 : (0 : ℝ) ≤ y c A := Nat.cast_nonneg _
    unfold gg
    split_ifs with hA
    · subst hA; simp
    · have hcard : (0 : ℝ) < A.card := by
        exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hA)
      have e : (A.card : ℝ) * (Sc (rosJobs K d y) c + ((∑ s ∈ A, rbar ε (rosJobs K d y) s) /
          A.card - rr ε (rosJobs K d y) c)) = (∑ s ∈ A, rbar ε (rosJobs K d y) s) +
          A.card * (Sc (rosJobs K d y) c - rr ε (rosJobs K d y) c) := by
        field_simp; ring
      have h1 : 0 ≤ (A.card : ℝ) * (Sc (rosJobs K d y) c - rr ε (rosJobs K d y) c) :=
        mul_nonneg hcard.le (by linarith [rr_le_Sc ε (rosJobs K d y) c])
      rw [mul_assoc, e]
      exact mul_le_mul_of_nonneg_left (by linarith) hy0
  have hb : ∀ s, rbar ε (rosJobs K d y) s ≤ (rosBusy K d y s : ℝ) * rbar ε (rosJobs K d y) s := by
    intro s
    by_cases hs : rosBusy K d y s = 0
    · rw [rbar_idle ε hε y hy s hs]; simp
    · have : (1 : ℝ) ≤ rosBusy K d y s := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hs
      nlinarith [rbar_nonneg ε (rosJobs K d y) s]
  calc ∑ s, rbar ε (rosJobs K d y) s
      ≤ ∑ s, (rosBusy K d y s : ℝ) * rbar ε (rosJobs K d y) s := Finset.sum_le_sum fun s _ => hb s
    _ = ∑ c, ∑ A, (y c A : ℝ) * ∑ s ∈ A, rbar ε (rosJobs K d y) s := busy_weighted y _
    _ ≤ _ := Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun A _ => ha c A

/-- expected Lyapunov value after each event -/
noncomputable def EWf (ε B θ : ℝ) (y : RosState K d) : RosEvent K d → ℝ
  | Sum.inl c => VV ε B θ (rosArrive K d y c)
  | Sum.inr p => VV ε B θ (rosRemove K d y p.1 p.2) +
      ((p.2.sort (· ≤ ·)).length : ℝ) * (4 * d * K / ε)

lemma ros_drift (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 ≤ lam) (hμ : 0 ≤ μ)
    (ε B θ : ℝ) (hε : 0 < ε) (y : RosState K d) (hy : InvL ∅ y) (t : ℕ)
    (ht : Tn (rosJobs K d y) = t + 1) :
    ∑ i, rosEventRate K d lam μ y i * (EWf ε B θ y i - VV ε B θ y) ≤
      lam * d + 2 * lam * d ^ 2 / K * (Tn (rosJobs K d y) : ℝ) + lam * (2 * K * Cg ε d) +
      μ * (∑ c, ∑ A, (y c A : ℝ) * A.card) * (d + 2 * K * Cg ε d + K * (4 * d * K / ε)) -
      2 * μ * ∑ s, rbar ε (rosJobs K d y) s +
      B * (1 - θ) * θ ^ t * (lam * θ - μ * ∑ c, ∑ A, (y c A : ℝ) * A.card) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  dsimp only [rosEventRate, EWf]
  have hC : (0 : ℝ) ≤ lam / (K.choose d : ℝ) := div_nonneg hlam (Nat.cast_nonneg _)
  have harr : ∀ c : JobType K d, lam / (K.choose d : ℝ) *
      (VV ε B θ (rosArrive K d y c) - VV ε B θ y) ≤
      lam / (K.choose d : ℝ) * (Phi (up (rosJobs K d y) c) - Phi (rosJobs K d y)) +
        lam / (K.choose d : ℝ) * (2 * K * Cg ε d + B * (θ ^ (t + 1) - θ ^ (t + 2))) := by
    intro c
    have := VV_arr ε B θ hε y hy c t ht
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hdep : ∀ c A, μ * (A.card : ℝ) * (y c A : ℝ) * (VV ε B θ (rosRemove K d y c A) +
      ((A.sort (· ≤ ·)).length : ℝ) * (4 * d * K / ε) - VV ε B θ y) ≤
      -(2 * μ) * ((y c A : ℝ) * A.card * (Sc (rosJobs K d y) c + gg ε (rosJobs K d y) c A)) +
      (μ * (d + 2 * K * Cg ε d + K * (4 * d * K / ε) + B * (θ ^ (t + 1) - θ ^ t))) *
        ((y c A : ℝ) * A.card) := by
    intro c A
    by_cases h0 : y c A = 0
    · simp [h0]
    · have hk : 1 ≤ y c A := Nat.one_le_iff_ne_zero.2 h0
      have h1 := VV_dep ε B θ hε y hy c A hk t ht
      have hlen : ((A.sort (· ≤ ·)).length : ℝ) ≤ K := by
        rw [Finset.length_sort]
        exact_mod_cast (Finset.card_le_univ A).trans (by simp)
      have hCp : (0 : ℝ) ≤ 4 * d * K / ε := by positivity
      have h2 : VV ε B θ (rosRemove K d y c A) + ((A.sort (· ≤ ·)).length : ℝ) *
          (4 * d * K / ε) - VV ε B θ y ≤
          -(2 * Sc (rosJobs K d y) c) + d - 2 * gg ε (rosJobs K d y) c A + 2 * K * Cg ε d +
            B * (θ ^ (t + 1) - θ ^ t) + K * (4 * d * K / ε) := by
        nlinarith [mul_le_mul_of_nonneg_right hlen hCp]
      have hr : 0 ≤ μ * (A.card : ℝ) * (y c A : ℝ) := by positivity
      calc μ * (A.card : ℝ) * (y c A : ℝ) * (VV ε B θ (rosRemove K d y c A) +
            ((A.sort (· ≤ ·)).length : ℝ) * (4 * d * K / ε) - VV ε B θ y)
          ≤ μ * (A.card : ℝ) * (y c A : ℝ) * (-(2 * Sc (rosJobs K d y) c) + d -
            2 * gg ε (rosJobs K d y) c A + 2 * K * Cg ε d + B * (θ ^ (t + 1) - θ ^ t) +
            K * (4 * d * K / ε)) := mul_le_mul_of_nonneg_left h2 hr
        _ = _ := by ring
  have hA := Finset.sum_le_sum fun c (_ : c ∈ (univ : Finset (JobType K d))) => harr c
  rw [Finset.sum_add_distrib, arr_total hd hdK lam, ← Finset.sum_mul, arr_rate_sum hdK] at hA
  have hD := Finset.sum_le_sum fun c (_ : c ∈ (univ : Finset (JobType K d))) =>
    Finset.sum_le_sum fun A (_ : A ∈ (univ : Finset (Finset (Fin K)))) => hdep c A
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hD
  have hkey := dep_key ε hε y hy
  have hμ2 := mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ 2 * μ)
  have hpatch : lam * (B * (θ ^ (t + 1) - θ ^ (t + 2))) +
      μ * B * (θ ^ (t + 1) - θ ^ t) * ∑ c, ∑ A, (y c A : ℝ) * A.card =
      B * (1 - θ) * θ ^ t * (lam * θ - μ * ∑ c, ∑ A, (y c A : ℝ) * A.card) := by ring
  linarith [hA, hD, hμ2, hpatch]

end ROS50

namespace ROS50

open RedundancyStab.IID Finset PS50

variable {K d : ℕ}

lemma rate_sum_ros (hdK : d ≤ K) (lam μ : ℝ) (y : RosState K d) :
    ∑ i, rosEventRate K d lam μ y i = lam + μ * ∑ c, ∑ A, (y c A : ℝ) * A.card := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  dsimp only [rosEventRate]
  rw [arr_rate_sum hdK]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by ring

lemma bt_nonneg (y : RosState K d) : 0 ≤ ∑ c, ∑ A, (y c A : ℝ) * A.card :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

lemma bt_le (y : RosState K d) (hb : ∀ s, rosBusy K d y s ≤ 1) :
    ∑ c, ∑ A, (y c A : ℝ) * A.card ≤ K := by
  rw [← busy_sum]
  calc ∑ s, (rosBusy K d y s : ℝ) ≤ ∑ _s : Fin K, (1 : ℝ) :=
        Finset.sum_le_sum fun s _ => by exact_mod_cast hb s
    _ = K := by simp

lemma bt_ge (hd : 1 ≤ d) (y : RosState K d) (hy : InvL ∅ y) (c : JobType K d)
    (hc : 1 ≤ rosJobs K d y c) : 1 ≤ ∑ c, ∑ A, (y c A : ℝ) * A.card := by
  obtain ⟨s, hs⟩ : c.1.Nonempty := by rw [← Finset.card_pos, c.2]; omega
  have hbs : rosBusy K d y s ≠ 0 := by
    intro h0
    have := hy.2.2.1 s (by simp) h0 c (by simp [typesAt, hs])
    omega
  rw [← busy_sum]
  calc (1 : ℝ) ≤ rosBusy K d y s := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hbs
    _ ≤ ∑ s', (rosBusy K d y s' : ℝ) :=
        Finset.single_le_sum (f := fun s => (rosBusy K d y s : ℝ)) (fun _ _ => Nat.cast_nonneg _)
          (mem_univ s)

set_option maxHeartbeats 1000000 in
lemma ros_good_empty (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hρ : lam / (μ * K) < 1) :
    TF50.GoodOn (rosJump K d lam μ) (InvL ∅) (rosEmpty K d) := by
  have hK0 : 0 < K := by omega
  have hK : (0 : ℝ) < K := by exact_mod_cast hK0
  have hlamK : lam < μ * K := by rwa [div_lt_one (by positivity)] at hρ
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = (μ * K - lam) / (2 * μ * K ^ 2) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεd]; exact div_pos (by linarith) (by positivity)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = μ / (2 * lam + 2 * μ) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_iff₀ (by positivity)]; linarith
  have hlθ : lam * θ ≤ μ / 2 := by
    rw [hθ, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hCg : 0 ≤ Cg ε d := by unfold Cg; positivity
  obtain ⟨D1, hD1⟩ : ∃ D1 : ℝ, D1 = d + 2 * K * Cg ε d + K * (4 * d * K / ε) := ⟨_, rfl⟩
  have hD10 : 0 ≤ D1 := by rw [hD1]; positivity
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = lam * d + lam * (2 * K * Cg ε d) + μ * K * D1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 2 * d ^ 2 * (μ * (1 - K * ε) - lam / K) := ⟨_, rfl⟩
  have he : μ * (1 - K * ε) - lam / K = (μ * K - lam) / (2 * K) := by
    rw [hεd]; field_simp; ring
  have hδ0 : 0 < δ := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h2 : 0 < (μ * K - lam) / (2 * K) := div_pos (by linarith) (by positivity)
    rw [hδ, he]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = lam + μ * K := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0]; positivity
  have hR0 : 0 < R := by rw [hR]; positivity
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = ⌈(C0 + R) / δ⌉₊ := ⟨_, rfl⟩
  have hN0' : C0 + R ≤ δ * N0 := by
    have := Nat.le_ceil ((C0 + R) / δ)
    rw [← hN0, div_le_iff₀ hδ0] at this; linarith
  have hθN : 0 < θ ^ N0 := pow_pos hθ0 _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * (C0 + R) / (μ * θ ^ N0) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBθ : B * θ ^ N0 * (μ / 4) = C0 + R := by rw [hB]; field_simp
  have h0 : ∀ (y : RosState K d) (i : RosEvent K d), 0 ≤ rosEventRate K d lam μ y i := by
    intro y i
    cases i with
    | inl c => exact div_nonneg hlam.le (Nat.cast_nonneg _)
    | inr p => exact mul_nonneg (mul_nonneg hμ.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hpos : ∀ y : RosState K d, 0 < ∑ i, rosEventRate K d lam μ y i := by
    intro y; rw [rate_sum_ros hdK]; nlinarith [bt_nonneg y]
  refine PS50.good_of_genOn (rosJump K d lam μ) (rosEventRate K d lam μ) (rosNext K d)
    (fun _ => rfl) h0 hpos (InvL ∅) (inv_closed lam μ) (VV ε B θ) (EWf ε B θ) ?_ ?_
    (rosEmpty K d) inv_empty ?_
  · intro y i hy hr
    cases i with
    | inl c =>
      dsimp only [rosNext, EWf]
      rw [tsum_eq_single (rosArrive K d y c)]
      · simp
      · intro z hz; simp [PMF.pure_apply, hz]
    | inr p =>
      obtain ⟨c, A⟩ := p
      dsimp only [rosNext, EWf]
      dsimp only [rosEventRate] at hr
      have hk : 1 ≤ y c A := by
        by_contra hn; push Not at hn
        have : y c A = 0 := by omega
        rw [this] at hr; simp at hr
      have hinv := inv_remove y hy c A hk
      have e : (A.sort (· ≤ ·)).toFinset = A := by simp
      have h := refill_VV ε B θ hε hK0 hB0 hθ0.le (by linarith) (A.sort (· ≤ ·))
        (Finset.sort_nodup _ _) (rosRemove K d y c A) (by rw [e]; exact hinv) 0 le_rfl
      simp only [add_zero] at h
      exact h
  · intro y i hy hr
    cases i with
    | inl c =>
      exact VV_nonneg ε B θ hK0 hB0 hθ0.le (by linarith) _ (inv_arrive y hy c).2.1
    | inr p =>
      obtain ⟨c, A⟩ := p
      dsimp only [EWf]
      dsimp only [rosEventRate] at hr
      have hk : 1 ≤ y c A := by
        by_contra hn; push Not at hn
        have : y c A = 0 := by omega
        rw [this] at hr; simp at hr
      exact add_nonneg (VV_nonneg ε B θ hK0 hB0 hθ0.le (by linarith) _
          (inv_remove y hy c A hk).2.1) (by positivity)
  · intro y hy hne
    obtain ⟨c, A, hk⟩ : ∃ c A, 1 ≤ y c A := by
      by_contra h; push Not at h
      apply hne; funext c A
      have := h c A
      simp only [rosEmpty, Pi.zero_apply]; omega
    have hjc := jobs_pos y c A hk
    obtain ⟨t, ht⟩ : ∃ t, Tn (rosJobs K d y) = t + 1 := by
      have : rosJobs K d y c ≤ Tn (rosJobs K d y) :=
        Finset.single_le_sum (f := rosJobs K d y) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      exact ⟨Tn (rosJobs K d y) - 1, by omega⟩
    have hdr := ros_drift hd hdK lam μ hlam.le hμ.le ε B θ hε y hy t ht
    rw [rate_sum_ros hdK]
    have hb1 := bt_ge hd y hy c hjc
    have hbK := bt_le y hy.2.1
    have hRb := rbar_sum_ge' ε hε (rosJobs K d y)
    have hm1 : μ * (∑ c, ∑ A, (y c A : ℝ) * A.card) * D1 ≤ μ * K * D1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbK hμ.le) hD10
    have hm2 := mul_le_mul_of_nonneg_left hRb (by linarith : (0 : ℝ) ≤ 2 * μ)
    rw [← hD1] at hdr
    have hlin : lam * d + 2 * lam * d ^ 2 / K * (Tn (rosJobs K d y) : ℝ) +
        lam * (2 * K * Cg ε d) + μ * (∑ c, ∑ A, (y c A : ℝ) * A.card) * D1 -
        2 * μ * ∑ s, rbar ε (rosJobs K d y) s ≤ C0 - δ * (Tn (rosJobs K d y) : ℝ) := by
      rw [hC0, hδ]
      have e2 : 2 * lam * (d : ℝ) ^ 2 / K * (Tn (rosJobs K d y) : ℝ) =
          2 * d ^ 2 * (lam / K) * (Tn (rosJobs K d y) : ℝ) := by ring
      rw [e2]
      linarith only [hm1, hm2]
    have hθt : 0 < θ ^ t := pow_pos hθ0 _
    have hμb := mul_le_mul_of_nonneg_left hb1 hμ.le
    have hb : lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card) ≤ -(μ / 2) := by
      linarith only [hμb, hlθ]
    have ha : 0 ≤ (1 - θ) - 1 / 2 := by linarith only [hθ1]
    have hX : ((1 - θ) - 1 / 2) * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ha (by linarith only [hb, hμ])
    have hg1 : (1 - θ) * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card)) ≤ -(μ / 4) := by
      have e : (1 - θ) * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card)) =
          1 / 2 * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card)) +
          ((1 - θ) - 1 / 2) * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card)) := by ring
      rw [e]; linarith only [hX, hb]
    have hg : B * (1 - θ) * θ ^ t * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card)) ≤
        -(B * θ ^ t * (μ / 4)) := by
      have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg hB0 hθt.le)
      have e : B * (1 - θ) * θ ^ t * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card)) =
          (B * θ ^ t) * ((1 - θ) * (lam * θ - μ * (∑ c, ∑ A, (y c A : ℝ) * A.card))) := by ring
      rw [e]; linarith only [this]
    have hT : ((Tn (rosJobs K d y) : ℕ) : ℝ) = t + 1 := by rw [ht]; push_cast; ring
    have hμD : μ * (∑ c, ∑ A, (y c A : ℝ) * A.card) ≤ μ * K := mul_le_mul_of_nonneg_left hbK hμ.le
    by_cases hcase : N0 ≤ t + 1
    · have h1 : (N0 : ℝ) ≤ (Tn (rosJobs K d y) : ℝ) := by rw [ht]; exact_mod_cast hcase
      have h2 := mul_le_mul_of_nonneg_left h1 hδ0.le
      have hBt : 0 ≤ B * θ ^ t * (μ / 4) :=
        mul_nonneg (mul_nonneg hB0 hθt.le) (by positivity)
      linarith
    · have htN : t ≤ N0 := by omega
      have hpow : θ ^ N0 ≤ θ ^ t := pow_le_pow_of_le_one hθ0.le (by linarith) htN
      have h3 : B * θ ^ N0 * (μ / 4) ≤ B * θ ^ t * (μ / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB0) (by positivity)
      have hTn : 0 ≤ δ * ((Tn (rosJobs K d y) : ℕ) : ℝ) := mul_nonneg hδ0.le (Nat.cast_nonneg _)
      linarith

end ROS50

open RedundancyStab.IID ProcessingNetworks.Stability in
theorem solution (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam)
    (hμ : 0 < μ) (hρ : lam / (μ * K) < 1) :
    PositiveRecurrent (psJump K d lam μ) (psRate K d lam μ) ∧
      ∀ x : RosState K d, (∃ m : ℕ, 0 < stepIter (rosJump K d lam μ) m (rosEmpty K d) x) →
        Recurrent (rosJump K d lam μ) x ∧
          meanReturnTime (rosJump K d lam μ) (rosRate K d lam μ) x < ⊤ := by
  exact ⟨PS50.ps_posrec hd hdK lam μ hlam hμ hρ,
    ROS50.ros_conj_of_good hdK lam μ hlam hμ (ROS50.ros_good_empty hd hdK lam μ hlam hμ hρ)⟩
