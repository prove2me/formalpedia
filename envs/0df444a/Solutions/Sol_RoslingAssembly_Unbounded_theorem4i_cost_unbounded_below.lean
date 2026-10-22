-- Prove2me | solution 1 for RoslingAssembly.Unbounded.theorem4i_cost_unbounded_below
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:13:20.131998+00:00
-- url     : https://prove2.me/submissions/29c958eb-e259-45fc-a89b-35fb82adcbfc

import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model
import Definitions.Def_RoslingAssembly_Unbounded_Perturb



namespace RoslingAssembly.Unbounded

open MeasureTheory


section Gen

variable {Ω : Type*} [MeasurableSpace Ω]

def AbsFin (μ : Measure Ω) (g : ℕ → Ω → ℝ) : Prop :=
  ∫⁻ ω, ∑' k, ENNReal.ofReal |g k ω| ∂μ ≠ ⊤

theorem cost_eq_integral {μ : Measure Ω} {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (h : AbsFin μ g) :
    Integrable (fun ω => ∑' k, g k ω) μ ∧
    (((∫⁻ ω, ∑' k, ENNReal.ofReal (g k ω) ∂μ : ENNReal) : EReal) -
      ((∫⁻ ω, ∑' k, ENNReal.ofReal (- g k ω) ∂μ : ENNReal) : EReal) =
      ((∫ ω, ∑' k, g k ω ∂μ : ℝ) : EReal)) := by
  set T : Ω → ENNReal := fun ω => ∑' k, ENNReal.ofReal |g k ω| with hTdef
  have hTm : Measurable T := Measurable.ennreal_tsum fun k => (hg k).abs.ennreal_ofReal
  have hae : ∀ᵐ ω ∂μ, T ω < ⊤ := ae_lt_top hTm h
  set Pm : Ω → ENNReal := fun ω => ∑' k, ENNReal.ofReal (g k ω) with hPm
  set Nm : Ω → ENNReal := fun ω => ∑' k, ENNReal.ofReal (- g k ω) with hNm
  have hPmm : Measurable Pm := Measurable.ennreal_tsum fun k => (hg k).ennreal_ofReal
  have hNmm : Measurable Nm := Measurable.ennreal_tsum fun k => (hg k).neg.ennreal_ofReal
  have hPle : ∀ ω, Pm ω ≤ T ω := fun ω =>
    ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hNle : ∀ ω, Nm ω ≤ T ω := fun ω =>
    ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (neg_le_abs _)
  have hPfin : ∫⁻ ω, Pm ω ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top h (lintegral_mono hPle)
  have hNfin : ∫⁻ ω, Nm ω ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top h (lintegral_mono hNle)
  have hPae : ∀ᵐ ω ∂μ, Pm ω < ⊤ := ae_lt_top hPmm hPfin
  have hNae : ∀ᵐ ω ∂μ, Nm ω < ⊤ := ae_lt_top hNmm hNfin
  have hF : ∀ᵐ ω ∂μ, ∑' k, g k ω = (Pm ω).toReal - (Nm ω).toReal := by
    filter_upwards [hae] with ω hω
    have hs : Summable fun k => |g k ω| := by
      have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal |g k ω|) hω.ne
      simpa [abs_nonneg] using this
    have hs1 : Summable fun k => max (g k ω) 0 :=
      Summable.of_nonneg_of_le (fun k => le_max_right _ _) (fun k => by
        rcases le_total (g k ω) 0 with h0 | h0
        · rw [max_eq_right h0]; exact abs_nonneg _
        · rw [max_eq_left h0]; exact le_abs_self _) hs
    have hs2 : Summable fun k => max (- g k ω) 0 :=
      Summable.of_nonneg_of_le (fun k => le_max_right _ _) (fun k => by
        rcases le_total (-g k ω) 0 with h0 | h0
        · rw [max_eq_right h0]; exact abs_nonneg _
        · rw [max_eq_left h0]; exact neg_le_abs _) hs
    have e1 : (Pm ω).toReal = ∑' k, max (g k ω) 0 := by
      simp only [hPm]
      rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
      simp [ENNReal.toReal_ofReal']
    have e2 : (Nm ω).toReal = ∑' k, max (- g k ω) 0 := by
      simp only [hNm]
      rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
      simp [ENNReal.toReal_ofReal']
    rw [e1, e2, ← Summable.tsum_sub hs1 hs2]
    congr 1
    funext k
    rcases le_total (g k ω) 0 with h0 | h0
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
  have hPi : Integrable (fun ω => (Pm ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hPmm.aemeasurable hPfin
  have hNi : Integrable (fun ω => (Nm ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hNmm.aemeasurable hNfin
  have hint : Integrable (fun ω => ∑' k, g k ω) μ :=
    (hPi.sub hNi).congr (by filter_upwards [hF] with ω hω using hω.symm)
  refine ⟨hint, ?_⟩
  have hI : ∫ ω, ∑' k, g k ω ∂μ = (∫⁻ ω, Pm ω ∂μ).toReal - (∫⁻ ω, Nm ω ∂μ).toReal := by
    rw [integral_congr_ae hF, integral_sub hPi hNi,
      integral_toReal hPmm.aemeasurable hPae, integral_toReal hNmm.aemeasurable hNae]
  rw [hI, EReal.coe_sub, EReal.coe_ennreal_toReal hPfin, EReal.coe_ennreal_toReal hNfin]

theorem ae_summable {μ : Measure Ω} {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (h : AbsFin μ g) : ∀ᵐ ω ∂μ, Summable fun k => g k ω := by
  have hTm : Measurable (fun ω => ∑' k, ENNReal.ofReal |g k ω|) :=
    Measurable.ennreal_tsum fun k => (hg k).abs.ennreal_ofReal
  filter_upwards [ae_lt_top hTm h] with ω hω
  have hs : Summable fun k => |g k ω| := by
    have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal |g k ω|) hω.ne
    simpa [abs_nonneg] using this
  exact hs.of_abs

theorem absFin_add {μ : Measure Ω} {g d : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (hd : ∀ k, Measurable (d k)) (h1 : AbsFin μ g) (h2 : AbsFin μ d) :
    AbsFin μ (fun k ω => g k ω + d k ω) := by
  unfold AbsFin at *
  have hm : Measurable (fun ω => ∑' k, ENNReal.ofReal |g k ω|) :=
    Measurable.ennreal_tsum fun k => (hg k).abs.ennreal_ofReal
  have : ∫⁻ ω, ∑' k, ENNReal.ofReal |g k ω + d k ω| ∂μ ≤
      ∫⁻ ω, (∑' k, ENNReal.ofReal |g k ω| + ∑' k, ENNReal.ofReal |d k ω|) ∂μ := by
    apply lintegral_mono
    intro ω
    simp only []
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun k => ?_
    calc ENNReal.ofReal |g k ω + d k ω| ≤ ENNReal.ofReal (|g k ω| + |d k ω|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ _ := ENNReal.ofReal_add_le
  refine ne_top_of_le_ne_top ?_ this
  rw [lintegral_add_left hm]
  exact ENNReal.add_ne_top.mpr ⟨h1, h2⟩

theorem integral_tsum_add {μ : Measure Ω} {g d : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (hd : ∀ k, Measurable (d k)) (h1 : AbsFin μ g) (h2 : AbsFin μ d) :
    ∫ ω, ∑' k, (g k ω + d k ω) ∂μ = ∫ ω, ∑' k, g k ω ∂μ + ∫ ω, ∑' k, d k ω ∂μ := by
  have i1 := (cost_eq_integral hg h1).1
  have i2 := (cost_eq_integral hd h2).1
  rw [← integral_add i1 i2]
  apply integral_congr_ae
  filter_upwards [ae_summable hg h1, ae_summable hd h2] with ω a b
  exact Summable.tsum_add a b

end Gen

namespace Model

variable (S : Model)

lemma succ_lt_of_mem (hT : S.IsTree) {y : ℕ} (hy : y ∈ S.items) : S.succ y + 1 ≤ y := by
  obtain ⟨h1, h2, h3⟩ := hT
  simp only [Model.items, Finset.mem_Icc] at hy
  by_cases hy1 : y = 1
  · subst hy1; simp [h2]
  · have := h3 y (by simp only [Finset.mem_Icc]; omega)
    omega

lemma succ_mem_of_ne_one (hT : S.IsTree) {y : ℕ} (hy : y ∈ S.items) (hy1 : y ≠ 1) :
    S.succ y ∈ S.items := by
  obtain ⟨h1, h2, h3⟩ := hT
  simp only [Model.items, Finset.mem_Icc] at hy ⊢
  have := h3 y (by simp only [Finset.mem_Icc]; omega)
  omega

lemma iter_le (hT : S.IsTree) (x : ℕ) :
    ∀ m, (∀ m' ∈ Finset.range m, S.succ^[m'] x ∈ S.items) → S.succ^[m] x + m ≤ x := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have h1 := ih (fun m' hm' => h m' (by simp only [Finset.mem_range] at hm' ⊢; omega))
    have h2 := h m (by simp)
    have h3 := S.succ_lt_of_mem hT h2
    rw [Function.iterate_succ_apply']
    omega

open Classical in
lemma A_sub (j : ℕ) : S.A j ⊆ S.items := by
  unfold Model.A; exact @Finset.filter_subset _ _ (fun _ => Classical.propDecidable _) _

open Classical in
lemma mem_A_iff (j k : ℕ) : k ∈ S.A j ↔ k ∈ S.items ∧
    ∃ n ∈ Finset.Icc 1 S.N, S.succ^[n] j = k ∧ ∀ m ∈ Finset.range n, S.succ^[m] j ∈ S.items := by
  unfold Model.A; exact @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _

lemma mem_A_lt (hT : S.IsTree) {j k : ℕ} (hk : k ∈ S.A j) : k < j := by
  rw [S.mem_A_iff] at hk
  simp only [Finset.mem_Icc] at hk
  obtain ⟨_, n, ⟨hn1, _⟩, hnk, hch⟩ := hk
  have := S.iter_le hT j n hch
  rw [hnk] at this
  omega

lemma A_one (hT : S.IsTree) : S.A 1 = ∅ := by
  ext k
  simp only [Finset.notMem_empty, iff_false]
  intro hk
  have := S.mem_A_lt hT hk
  have h1 := hT.1
  have hk2 : k ∈ S.items := S.A_sub 1 hk
  simp only [Model.items, Finset.mem_Icc] at hk2
  omega

lemma A_succ (hT : S.IsTree) {j : ℕ} (hj : j ∈ S.items) (hs : S.succ j ∈ S.items) :
    S.A j = insert (S.succ j) (S.A (S.succ j)) := by
  have hjs := S.succ_lt_of_mem hT hj
  have hN : j ≤ S.N := by simpa [Model.items] using (Finset.mem_Icc.mp hj).2
  ext k
  rw [Finset.mem_insert, S.mem_A_iff, S.mem_A_iff]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨hk, n, ⟨hn1, hnN⟩, hnk, hch⟩
    by_cases hn : n = 1
    · subst hn
      left
      simpa using hnk.symm
    · right
      refine ⟨hk, n - 1, ⟨by omega, by omega⟩, ?_, ?_⟩
      · have : n = (n - 1) + 1 := by omega
        rw [← hnk, this, Function.iterate_succ_apply]
        simp
      · intro m hm
        have := hch (m + 1) (by simp only [Finset.mem_range] at hm ⊢; omega)
        rwa [Function.iterate_succ_apply] at this
  · rintro (h | ⟨hk, n, ⟨hn1, hnN⟩, hnk, hch⟩)
    · refine ⟨h ▸ hs, 1, ⟨le_rfl, ?_⟩, by simp [h], ?_⟩
      · have := hT.1; omega
      · intro m hm
        have : m = 0 := by simp only [Finset.mem_range] at hm; omega
        subst this
        simpa using hj
    · have hle := S.iter_le hT _ n hch
      rw [hnk] at hle
      have hk1 : 1 ≤ k := by
        have := (Finset.mem_Icc.mp hk).1
        exact this
      refine ⟨hk, n + 1, ⟨by omega, by omega⟩, ?_, ?_⟩
      · rw [Function.iterate_succ_apply]; exact hnk
      · intro m hm
        cases m with
        | zero => simpa using hj
        | succ m =>
          rw [Function.iterate_succ_apply]
          exact hch m (by simp only [Finset.mem_range] at hm ⊢; omega)

lemma M_succ (hT : S.IsTree) {j : ℕ} (hj : j ∈ S.items) :
    S.M j = S.l j + S.M (S.succ j) := by
  have hj0 : j ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1; omega
  by_cases hs : S.succ j ∈ S.items
  · have hs0 : S.succ j ≠ 0 := by
      have := (Finset.mem_Icc.mp hs).1; omega
    have hnot : S.succ j ∉ S.A (S.succ j) := fun h => by
      have := S.mem_A_lt hT h; omega
    unfold Model.M
    rw [if_neg hj0, if_neg hs0, S.A_succ hT hj hs, Finset.sum_insert hnot]
  · have hj1 : j = 1 := by
      by_contra hne
      exact hs (S.succ_mem_of_ne_one hT hj hne)
    subst hj1
    unfold Model.M
    rw [S.A_one hT, hT.2.1]
    simp

open Classical in
lemma mem_B_iff (i k : ℕ) : k ∈ S.B i ↔ k ∈ S.items ∧ i ∈ S.A k := by
  simp [Model.B]

lemma B_sub (i : ℕ) : S.B i ⊆ S.items := fun k hk => ((S.mem_B_iff i k).mp hk).1

lemma mem_P_iff (i j : ℕ) : j ∈ S.P i ↔ j ∈ S.items ∧ S.succ j = i := by
  unfold Model.P; exact Finset.mem_filter

lemma P_mem_B (hT : S.IsTree) {i : ℕ} (hi : i ∈ S.items) {i' : ℕ}
    (hi' : i' ∈ insert i (S.B i)) {j : ℕ} (hj : j ∈ S.P i') : j ∈ S.B i := by
  rw [S.mem_P_iff] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hi'i : i' ∈ S.items := by
    rcases Finset.mem_insert.mp hi' with h | h
    · rw [h]; exact hi
    · exact S.B_sub i h
  rw [S.mem_B_iff]
  refine ⟨hj1, ?_⟩
  rw [S.A_succ hT hj1 (hj2 ▸ hi'i), hj2]
  rcases Finset.mem_insert.mp hi' with h | h
  · rw [h]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((S.mem_B_iff i i').mp h).2

/-- the extra amount ordered of item `j` in Lean period `k` -/
noncomputable def ext (i : ℕ) (δ : ℝ) (j k : ℕ) : ℝ :=
  open Classical in if j ∈ insert i (S.B i) ∧ S.Mmax i - S.M j ≤ k then δ else 0

lemma perturb_apply (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) (k : ℕ)
    (x : Fin k → ℝ) (j : ℕ) : S.perturb π i δ k x j = π k x j + S.ext i δ j k := by
  unfold Model.perturb Model.ext
  congr 1

lemma ext_nonneg (i : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (j k : ℕ) : 0 ≤ S.ext i δ j k := by
  unfold Model.ext; split_ifs <;> simp [hδ]

lemma ext_mono (i : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) {a b : ℕ} (hab : a ≤ b) :
    S.ext i δ j a ≤ S.ext i δ j b := by
  unfold Model.ext
  by_cases h : j ∈ insert i (S.B i) ∧ S.Mmax i - S.M j ≤ a
  · rw [if_pos h, if_pos ⟨h.1, by omega⟩]
  · rw [if_neg h]; split_ifs <;> simp [hδ]

lemma Y_perturb (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) (ω : ℕ → ℝ) (k j : ℕ) :
    Y (S.perturb π i δ) ω k j = Y π ω k j + S.ext i δ j k := by
  unfold Y; rw [S.perturb_apply]

lemma pos_perturb (x0 : ℕ → ℕ → ℝ) (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ)
    (ω : ℕ → ℝ) (j k s : ℕ) :
    pos x0 (S.perturb π i δ) ω j k s =
      pos x0 π ω j k s + (if s ≤ k then S.ext i δ j (k - s) else 0) := by
  unfold pos
  by_cases h : s ≤ k
  · simp only [if_pos h, S.Y_perturb]; ring
  · simp only [if_neg h]; ring

theorem perturbation_feasible_core (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (i : ℕ) (hi : i ∈ S.items) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π)
    (hπ : S.Feasible x0 π) :
    IsMeasurablePolicy (S.perturb π i δ) ∧ S.Feasible x0 (S.perturb π i δ) := by
  refine ⟨?_, ?_⟩
  · intro k j
    have : (fun x : Fin k → ℝ => S.perturb π i δ k x j) = fun x => π k x j + S.ext i δ j k := by
      funext x; exact S.perturb_apply π i δ k x j
    rw [this]
    exact (hπm k j).add measurable_const
  · unfold Model.Feasible at hπ ⊢
    filter_upwards [hπ] with ω hω k i' hi'
    obtain ⟨h1, h2⟩ := hω k i' hi'
    refine ⟨?_, ?_⟩
    · rw [S.pos_perturb, S.Y_perturb]
      have e1 := S.ext_nonneg i hδ i' k
      split_ifs with hk
      · have := S.ext_mono i hδ i' (a := k - 1) (b := k) (by omega)
        linarith
      · linarith
    · intro j hj
      rw [S.Y_perturb, S.pos_perturb]
      have key : S.ext i δ i' k ≤ (if S.l j ≤ k then S.ext i δ j (k - S.l j) else 0) := by
        by_cases hc : i' ∈ insert i (S.B i) ∧ S.Mmax i - S.M i' ≤ k
        · have hjB := S.P_mem_B hT hi hc.1 hj
          have hjM := S.M_succ hT (((S.mem_P_iff i' j).mp hj).1)
          rw [((S.mem_P_iff i' j).mp hj).2] at hjM
          have hmax : S.M j ≤ S.Mmax i :=
            Finset.le_sup (f := S.M) (Finset.mem_insert_of_mem hjB)
          have hlk : S.l j ≤ k := by omega
          rw [if_pos hlk]
          unfold Model.ext
          rw [if_pos hc, if_pos ⟨Finset.mem_insert_of_mem hjB, by omega⟩]
        · have : S.ext i δ i' k = 0 := by unfold Model.ext; rw [if_neg hc]
          rw [this]
          split_ifs
          · exact S.ext_nonneg i hδ _ _
          · exact le_rfl
      have h3 := h2 j hj
      linarith


lemma tail_hasSum {α δ : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (a : ℕ) :
    HasSum (fun k : ℕ => if a ≤ k then δ * α ^ k else 0) (δ * α ^ a / (1 - α)) := by
  rw [← hasSum_nat_add_iff' a]
  have hz : ∑ i ∈ Finset.range a, (if a ≤ i then δ * α ^ i else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [if_neg]; simpa using hi)
  have : ∀ n : ℕ, (if a ≤ n + a then δ * α ^ (n + a) else 0) = (δ * α ^ a) * α ^ n := by
    intro n; rw [if_pos (by omega)]; ring
  simp only [this, hz, sub_zero]
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left (δ * α ^ a)
  simpa [div_eq_mul_inv, mul_assoc] using h

lemma pow_ident (a : ℝ) (ha : a ≠ 0) (lj lI Mj MI Msj MsI Mm : ℕ) (h1 : Mj = lj + Msj)
    (h2 : MI = lI + MsI) (h3 : Mj ≤ Mm) (h4 : MI ≤ Mm) :
    a ^ lj * a ^ (Mm - Mj) = a ^ (Mm - MI) * a ^ lI * a ^ (-((Msj : ℤ) - MsI)) := by
  have e : ∀ n : ℕ, a ^ n = a ^ (n : ℤ) := fun n => (zpow_natCast a n).symm
  simp only [e]
  rw [← zpow_add₀ ha, ← zpow_add₀ ha, ← zpow_add₀ ha]
  congr 1
  omega

lemma backlog_measurable [IsProbabilityMeasure S.ν] : Measurable S.backlog := by
  unfold Model.backlog
  have : SFinite S.leadDemandLaw := by unfold Model.leadDemandLaw; infer_instance
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => max (p.2 - p.1) 0) :=
    ((measurable_snd.sub measurable_fst).max measurable_const).stronglyMeasurable
  exact (hm.integral_prod_right').measurable

lemma Y_measurable (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π) (k i : ℕ) :
    Measurable (fun ω : ℕ → ℝ => Y π ω k i) :=
  (hπm k i).comp (measurable_pi_lambda _ fun j => measurable_pi_apply (j : ℕ))

lemma stageCost_measurable [IsProbabilityMeasure S.ν] (π : RoslingAssembly.SeriesEquiv.Policy)
    (hπm : IsMeasurablePolicy π) (k : ℕ) : Measurable (fun ω => S.stageCost π ω k) := by
  unfold Model.stageCost
  refine Measurable.add (Finset.measurable_sum _ fun i _ => measurable_const.mul
    (Y_measurable π hπm k i)) (measurable_const.mul
    (S.backlog_measurable.comp (Y_measurable π hπm k 1)))

lemma one_not_mem_T (hT : S.IsTree) {i : ℕ} (hi : i ∈ Finset.Icc 2 S.N) :
    1 ∉ insert i (S.B i) := by
  intro h
  rcases Finset.mem_insert.mp h with h | h
  · simp only [Finset.mem_Icc] at hi; omega
  · have := ((S.mem_B_iff i 1).mp h).2
    rw [S.A_one hT] at this
    simp at this

lemma i_not_mem_B (hT : S.IsTree) (i : ℕ) : i ∉ S.B i := by
  intro h
  have := S.mem_A_lt hT ((S.mem_B_iff i i).mp h).2
  omega

lemma stageCost_perturb (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) (ω : ℕ → ℝ)
    (k : ℕ) (h1 : S.ext i δ 1 k = 0) :
    S.stageCost (S.perturb π i δ) ω k = S.stageCost π ω k +
      ∑ j ∈ S.items, S.α ^ S.l j * S.h j * S.ext i δ j k := by
  unfold Model.stageCost
  simp only [S.Y_perturb, h1, add_zero, mul_add, Finset.sum_add_distrib]
  ring

lemma absFin_of_cost {μ : Measure (ℕ → ℝ)} {g : ℕ → (ℕ → ℝ) → ℝ} (hg : ∀ k, Measurable (g k))
    {J : ℝ}
    (hJ : ((∫⁻ ω, ∑' k, ENNReal.ofReal (g k ω) ∂μ : ENNReal) : EReal) -
      ((∫⁻ ω, ∑' k, ENNReal.ofReal (- g k ω) ∂μ : ENNReal) : EReal) = (J : EReal)) :
    AbsFin μ g := by
  set A := ∫⁻ ω, ∑' k, ENNReal.ofReal (g k ω) ∂μ with hA
  set B := ∫⁻ ω, ∑' k, ENNReal.ofReal (- g k ω) ∂μ with hB
  have hAB : A ≠ ⊤ ∧ B ≠ ⊤ := by
    by_cases hA' : A = ⊤
    · exfalso
      rw [hA', EReal.coe_ennreal_top] at hJ
      by_cases hB' : B = ⊤
      · rw [hB', EReal.coe_ennreal_top, EReal.sub_top] at hJ; simp at hJ
      · have h3 : ((B : ENNReal) : EReal) ≠ ⊤ := by
          rw [Ne, EReal.coe_ennreal_eq_top_iff]; exact hB'
        rw [EReal.top_sub h3] at hJ
        simp at hJ
    · refine ⟨hA', ?_⟩
      intro hB'
      rw [hB', EReal.coe_ennreal_top, EReal.sub_top] at hJ
      simp at hJ
  have hm : Measurable (fun ω => ∑' k, ENNReal.ofReal (g k ω)) :=
    Measurable.ennreal_tsum fun k => (hg k).ennreal_ofReal
  have : ∫⁻ ω, ∑' k, ENNReal.ofReal |g k ω| ∂μ = A + B := by
    rw [hA, hB, ← lintegral_add_left hm]
    congr 1
    funext ω
    rw [← ENNReal.tsum_add]
    congr 1
    funext k
    rcases le_total 0 (g k ω) with h0 | h0
    · rw [abs_of_nonneg h0, ENNReal.ofReal_of_nonpos (by linarith : -g k ω ≤ 0), add_zero]
    · rw [abs_of_nonpos h0, ENNReal.ofReal_of_nonpos h0, zero_add]
  unfold AbsFin
  rw [this]
  exact ENNReal.add_ne_top.mpr hAB

lemma ext_hasSum (i : ℕ) {δ : ℝ} (j : ℕ) (hα0 : 0 ≤ S.α) (hα1 : S.α < 1) :
    HasSum (fun k : ℕ => S.α ^ k * S.ext i δ j k)
      (if j ∈ insert i (S.B i) then δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α) else 0) := by
  by_cases hj : j ∈ insert i (S.B i)
  · rw [if_pos hj]
    have := tail_hasSum (δ := δ) hα0 hα1 (S.Mmax i - S.M j)
    convert this using 1
    funext k
    unfold Model.ext
    by_cases hk : S.Mmax i - S.M j ≤ k
    · rw [if_pos ⟨hj, hk⟩, if_pos hk]; ring
    · rw [if_neg (fun h => hk h.2), if_neg hk]; ring
  · rw [if_neg hj]
    convert hasSum_zero using 1
    funext k
    unfold Model.ext
    rw [if_neg (fun h => hj h.1)]; ring

lemma term_eq (hT : S.IsTree) (hα : S.α ≠ 0) {i : ℕ} (hi : i ∈ S.items) (δ : ℝ) {j : ℕ}
    (hj : j ∈ insert i (S.B i)) :
    S.α ^ S.l j * S.h j * (δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α)) =
      δ * S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i *
        (S.h j * S.α ^ (-((S.M (S.succ j) : ℤ) - (S.M (S.succ i) : ℤ)))) / (1 - S.α) := by
  have hjI : j ∈ S.items := by
    rcases Finset.mem_insert.mp hj with h | h
    · rw [h]; exact hi
    · exact S.B_sub i h
  have h1 := S.M_succ hT hjI
  have h2 := S.M_succ hT hi
  have h3 : S.M j ≤ S.Mmax i := Finset.le_sup (f := S.M) hj
  have h4 : S.M i ≤ S.Mmax i := Finset.le_sup (f := S.M) (Finset.mem_insert_self _ _)
  have key := pow_ident S.α hα (S.l j) (S.l i) (S.M j) (S.M i) (S.M (S.succ j)) (S.M (S.succ i))
    (S.Mmax i) h1 h2 h3 h4
  calc S.α ^ S.l j * S.h j * (δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α))
      = δ * S.h j * (S.α ^ S.l j * S.α ^ (S.Mmax i - S.M j)) / (1 - S.α) := by ring
    _ = _ := by rw [key]; ring

lemma Dval_eq (hT : S.IsTree) (hα : S.α ≠ 0) {i : ℕ} (hi : i ∈ S.items) (δ : ℝ) :
    ∑ j ∈ S.items, S.α ^ S.l j * S.h j *
      (if j ∈ insert i (S.B i) then δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α) else 0) =
    δ * S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i *
      (S.h i + ∑ k ∈ S.B i,
        S.h k * S.α ^ (-((S.M (S.succ k) : ℤ) - (S.M (S.succ i) : ℤ)))) / (1 - S.α) := by
  have hTsub : insert i (S.B i) ⊆ S.items := by
    intro j hj
    rcases Finset.mem_insert.mp hj with h | h
    · rw [h]; exact hi
    · exact S.B_sub i h
  have e1 : ∑ j ∈ S.items, S.α ^ S.l j * S.h j *
      (if j ∈ insert i (S.B i) then δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α) else 0) =
      ∑ j ∈ insert i (S.B i), S.α ^ S.l j * S.h j *
        (δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α)) := by
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTsub]
  rw [e1]
  rw [Finset.sum_congr rfl (fun j hj => S.term_eq hT hα hi δ hj)]
  rw [Finset.sum_insert (S.i_not_mem_B hT i), ← Finset.sum_div, ← Finset.mul_sum]
  simp only [sub_self, Int.cast_zero, neg_zero, zpow_zero, mul_one]
  ring

theorem total_cost_core [IsProbabilityMeasure S.ν] (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hα0 : 0 < S.α) (hα1 : S.α < 1)
    (i : ℕ) (hi : i ∈ Finset.Icc 2 S.N) (δ : ℝ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π)
    (J : ℝ) (hJ : S.cost π = (J : EReal)) :
    S.cost (S.perturb π i δ) =
      ((J + δ * S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i *
          (S.h i + ∑ k ∈ S.B i,
            S.h k * S.α ^ (-((S.M (S.succ k) : ℤ) - (S.M (S.succ i) : ℤ)))) / (1 - S.α) : ℝ) :
        EReal) := by
  haveI : IsProbabilityMeasure S.demandSeq := by unfold Model.demandSeq; infer_instance
  have hiI : i ∈ S.items := by
    simp only [Model.items, Finset.mem_Icc] at hi ⊢; omega
  have hone := S.one_not_mem_T hT hi
  set μ := S.demandSeq with hμ
  set g : ℕ → (ℕ → ℝ) → ℝ := fun k ω => S.α ^ k * S.stageCost π ω k with hg
  have hgm : ∀ k, Measurable (g k) := fun k =>
    measurable_const.mul (S.stageCost_measurable π hπm k)
  have hJ' : ((∫⁻ ω, ∑' k, ENNReal.ofReal (g k ω) ∂μ : ENNReal) : EReal) -
      ((∫⁻ ω, ∑' k, ENNReal.ofReal (- g k ω) ∂μ : ENNReal) : EReal) = (J : EReal) := hJ
  have habs := absFin_of_cost hgm hJ'
  obtain ⟨_, hgI⟩ := cost_eq_integral hgm habs
  have hJint : ∫ ω, ∑' k, g k ω ∂μ = J := by
    rw [hJ'] at hgI
    exact (EReal.coe_eq_coe_iff.mp hgI).symm
  set c : ℕ → ℝ := fun j => S.α ^ S.l j * S.h j with hc
  set d : ℕ → (ℕ → ℝ) → ℝ := fun k _ => S.α ^ k * ∑ j ∈ S.items, c j * S.ext i δ j k with hd
  have hdm : ∀ k, Measurable (d k) := fun k => measurable_const
  have hdS : HasSum (fun k : ℕ => S.α ^ k * ∑ j ∈ S.items, c j * S.ext i δ j k)
      (∑ j ∈ S.items, c j *
        (if j ∈ insert i (S.B i) then δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α) else 0)) := by
    have := hasSum_sum (s := S.items) (fun j _ => (S.ext_hasSum i (δ := δ) j hα0.le hα1).mul_left (c j))
    have e : (fun k : ℕ => S.α ^ k * ∑ j ∈ S.items, c j * S.ext i δ j k) =
        fun b => ∑ i_1 ∈ S.items, c i_1 * (S.α ^ b * S.ext i δ i_1 b) := by
      funext k
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]; exact this
  have habsd : AbsFin μ d := by
    unfold AbsFin
    simp only [hd, lintegral_const, measure_univ, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => abs_nonneg _) hdS.summable.abs]
    exact ENNReal.ofReal_ne_top
  have hstage : ∀ k ω, S.α ^ k * S.stageCost (S.perturb π i δ) ω k = g k ω + d k ω := by
    intro k ω
    have h1 : S.ext i δ 1 k = 0 := by unfold Model.ext; rw [if_neg (fun h => hone h.1)]
    rw [S.stageCost_perturb π i δ ω k h1]
    simp only [hg, hd, hc]
    rw [mul_add]
  have hg'm : ∀ k, Measurable (fun ω => g k ω + d k ω) := fun k => (hgm k).add (hdm k)
  have habs' := absFin_add hgm hdm habs habsd
  have hcost' : S.cost (S.perturb π i δ) =
      (((∫⁻ ω, ∑' k, ENNReal.ofReal (g k ω + d k ω) ∂μ : ENNReal) : EReal) -
      ((∫⁻ ω, ∑' k, ENNReal.ofReal (- (g k ω + d k ω)) ∂μ : ENNReal) : EReal)) := by
    unfold Model.cost
    simp only [hstage]
    rfl
  rw [hcost', (cost_eq_integral hg'm habs').2, integral_tsum_add hgm hdm habs habsd, hJint]
  have hdint : ∫ ω, ∑' k, d k ω ∂μ = ∑ j ∈ S.items, c j *
        (if j ∈ insert i (S.B i) then δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α) else 0) := by
    simp only [hd]
    rw [hdS.tsum_eq]
    simp
  rw [hdint, S.Dval_eq hT hα0.ne' hiI δ]

lemma stageCost_perturb_gen (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) (ω : ℕ → ℝ)
    (k : ℕ) :
    S.stageCost (S.perturb π i δ) ω k = S.stageCost π ω k +
      ∑ j ∈ S.items, S.α ^ S.l j * S.h j * S.ext i δ j k +
      S.α ^ S.l 1 * (S.p + S.H1) *
        (S.backlog (Y π ω k 1 + S.ext i δ 1 k) - S.backlog (Y π ω k 1)) := by
  unfold Model.stageCost
  simp only [S.Y_perturb, mul_add, Finset.sum_add_distrib]
  ring

lemma leadLaw_finite [IsProbabilityMeasure S.ν] : IsFiniteMeasure S.leadDemandLaw := by
  unfold Model.leadDemandLaw; infer_instance

lemma leadLaw_prob [IsProbabilityMeasure S.ν] : IsProbabilityMeasure S.leadDemandLaw := by
  unfold Model.leadDemandLaw
  exact Measure.isProbabilityMeasure_map (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).aemeasurable

lemma leadLaw_integrable [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) :
    Integrable id S.leadDemandLaw := by
  unfold Model.leadDemandLaw
  rw [integrable_map_measure aestronglyMeasurable_id
    (by exact (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).aemeasurable)]
  show Integrable (fun x : Fin (S.l 1 + 1) → ℝ => ∑ j, x j) _
  exact integrable_finset_sum _ fun j _ => integrable_eval (μ := fun _ : Fin (S.l 1 + 1) => S.ν) hν

lemma bl_integrable [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) S.leadDemandLaw := by
  haveI := S.leadLaw_finite
  have h1 : Integrable (fun x : ℝ => |x| + |y|) S.leadDemandLaw :=
    ((S.leadLaw_integrable hν).norm).add (integrable_const _)
  refine Integrable.mono' h1 ((measurable_id.sub measurable_const).max
    measurable_const).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ (by positivity)
  have := abs_sub (x) y
  have h2 := le_abs_self (x - y)
  linarith [abs_sub x y]

lemma backlog_nonneg (y : ℝ) : 0 ≤ S.backlog y :=
  integral_nonneg fun x => le_max_right _ _

lemma backlog_bound [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, S.backlog y ≤ M + |y| := by
  haveI := S.leadLaw_finite
  refine ⟨∫ x, |x| ∂S.leadDemandLaw, integral_nonneg fun x => abs_nonneg x, fun y => ?_⟩
  have h1 : Integrable (fun x : ℝ => |x| + |y|) S.leadDemandLaw :=
    ((S.leadLaw_integrable hν).norm).add (integrable_const _)
  have : S.backlog y ≤ ∫ x, (|x| + |y|) ∂S.leadDemandLaw := by
    unfold Model.backlog
    refine integral_mono (S.bl_integrable hν y) h1 fun x => ?_
    refine max_le ?_ (by positivity)
    linarith [abs_sub x y, le_abs_self (x - y), abs_nonneg (x-y), abs_nonneg x, abs_nonneg y,
      abs_sub_comm x y]
  have hI : Integrable (fun x : ℝ => |x|) S.leadDemandLaw := by
    simpa using (S.leadLaw_integrable hν).norm
  rw [integral_add hI (integrable_const _)] at this
  haveI hp := S.leadLaw_prob
  simpa using this

lemma backlog_anti [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) (y e : ℝ) (he : 0 ≤ e) :
    S.backlog (y + e) ≤ S.backlog y := by
  unfold Model.backlog
  exact integral_mono (S.bl_integrable hν _) (S.bl_integrable hν _) fun x =>
    max_le_max (by linarith) le_rfl

lemma demand_prob [IsProbabilityMeasure S.ν] : IsProbabilityMeasure S.demandSeq := by
  unfold Model.demandSeq; infer_instance

lemma eval_integrable [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) (r : ℕ) :
    Integrable (fun ω : ℕ → ℝ => |ω r|) S.demandSeq := by
  have hg : Integrable (fun x : ℝ => |x|) S.ν :=
    Integrable.congr hν.norm (ae_of_all _ fun x => Real.norm_eq_abs x)
  have h := measurePreserving_eval_infinitePi (fun _ : ℕ => S.ν) r
  have hg' : Integrable (fun x : ℝ => |x|) (Measure.map (Function.eval r) S.demandSeq) := by
    unfold Model.demandSeq; rw [h.map_eq]; exact hg
  exact Integrable.comp_measurable hg' h.measurable

lemma eval_integral [IsProbabilityMeasure S.ν] (r : ℕ) :
    ∫ ω, |ω r| ∂S.demandSeq = ∫ x, |x| ∂S.ν := by
  unfold Model.demandSeq
  have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => S.ν) r)
  have := integral_map (μ := Measure.infinitePi fun _ : ℕ => S.ν) (φ := Function.eval r)
    (f := fun x : ℝ => |x|)
    h.measurable.aemeasurable (by
      rw [h.map_eq]; exact (measurable_id.abs).aestronglyMeasurable)
  rw [h.map_eq] at this
  exact this.symm

/-- the dominating function `α^k (P + Q ∑_{r<k} |ω_r|)` -/
def Sk (k : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ r ∈ Finset.range k, |ω r|

lemma Sk_measurable (k : ℕ) : Measurable (Sk k) :=
  Finset.measurable_sum _ fun r _ => (measurable_pi_apply r).abs

lemma absFin_of_bound [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hα0 : 0 < S.α) (hα1 : S.α < 1)
    {g : ℕ → (ℕ → ℝ) → ℝ} (hg : ∀ k, Measurable (g k))
    (hb : ∀ k ω, |g k ω| ≤ S.α ^ k * (P + Q * Sk k ω)) : AbsFin S.demandSeq g := by
  haveI := S.demand_prob
  set e := ∫ x, |x| ∂S.ν with he
  have hint : ∀ k, Integrable (fun ω => S.α ^ k * (P + Q * Sk k ω)) S.demandSeq := by
    intro k
    refine Integrable.const_mul (Integrable.add (integrable_const _) (Integrable.const_mul ?_ _)) _
    exact integrable_finset_sum _ fun r _ => S.eval_integrable hν r
  have hval : ∀ k, ∫ ω, S.α ^ k * (P + Q * Sk k ω) ∂S.demandSeq = S.α ^ k * (P + Q * (k * e)) := by
    intro k
    simp only [Sk]
    rw [integral_const_mul, integral_add (integrable_const _) (Integrable.const_mul
      (integrable_finset_sum _ fun r _ => S.eval_integrable hν r) _), integral_const_mul]
    rw [integral_finset_sum _ fun r _ => S.eval_integrable hν r]
    simp [S.eval_integral, he]
  have hnn : ∀ k ω, 0 ≤ S.α ^ k * (P + Q * Sk k ω) := fun k ω => by
    have : 0 ≤ Sk k ω := Finset.sum_nonneg fun r _ => abs_nonneg _
    positivity
  have hsum : Summable fun k : ℕ => S.α ^ k * (P + Q * (k * e)) := by
    have h1 := (summable_geometric_of_lt_one hα0.le hα1).mul_left P
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 (r := S.α)
      (by rw [Real.norm_eq_abs, abs_of_pos hα0]; exact hα1)).mul_left (Q * e)
    have e : (fun k : ℕ => S.α ^ k * (P + Q * (k * e))) =
        fun i : ℕ => P * S.α ^ i + Q * e * ((i : ℝ) ^ 1 * S.α ^ i) := by
      funext k; simp; ring
    rw [e]; exact h1.add h2
  have hmeas : ∀ k, Measurable (fun ω => S.α ^ k * (P + Q * Sk k ω)) := fun k =>
    measurable_const.mul (measurable_const.add (measurable_const.mul (Sk_measurable k)))
  unfold AbsFin
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω => ENNReal.tsum_le_tsum fun k =>
    ENNReal.ofReal_le_ofReal (hb k ω))
  rw [lintegral_tsum fun k => (hmeas k).ennreal_ofReal.aemeasurable]
  have : ∀ k, ∫⁻ ω, ENNReal.ofReal (S.α ^ k * (P + Q * Sk k ω)) ∂S.demandSeq =
      ENNReal.ofReal (S.α ^ k * (P + Q * (k * e))) := by
    intro k
    rw [← hval k, ofReal_integral_eq_lintegral_ofReal (hint k) (ae_of_all _ (hnn k))]
  simp only [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg _ hsum]
  · exact ENNReal.ofReal_ne_top
  · intro k
    have := hval k ▸ integral_nonneg (hnn k)
    exact this

/-- the "never order" policy: `Y_{j,k} = x0 j 1 - ∑_{r<k} ξ_r` -/
def neverOrder (x0 : ℕ → ℕ → ℝ) : RoslingAssembly.SeriesEquiv.Policy :=
  fun k h j => x0 j 1 - ∑ r : Fin k, h r

lemma Y_never (x0 : ℕ → ℕ → ℝ) (ω : ℕ → ℝ) (k j : ℕ) :
    Y (neverOrder x0) ω k j = x0 j 1 - ∑ r ∈ Finset.range k, ω r := by
  unfold Y neverOrder
  rw [Fin.sum_univ_eq_sum_range (fun r => ω r) k]

lemma never_measurable (x0 : ℕ → ℕ → ℝ) : IsMeasurablePolicy (neverOrder x0) := by
  intro k j
  unfold neverOrder
  exact measurable_const.sub (Finset.measurable_sum _ fun r _ => measurable_pi_apply r)

lemma pos_never (x0 : ℕ → ℕ → ℝ) (ω : ℕ → ℝ) (j k s : ℕ) :
    pos x0 (neverOrder x0) ω j k s =
      (if s ≤ k then x0 j 1 else x0 j (s - k)) - ∑ r ∈ Finset.range k, ω r := by
  unfold pos
  by_cases h : s ≤ k
  · simp only [if_pos h, Y_never]
    have := Finset.sum_range_add_sum_Ico ω (Nat.sub_le k s)
    linarith
  · simp only [if_neg h]

lemma x0_anti {x0 : ℕ → ℕ → ℝ} (hx0 : S.WellFormed x0) {j : ℕ} (hj : j ∈ S.items) {t u : ℕ} (ht : 1 ≤ t)
    (htu : t ≤ u) : x0 j u ≤ x0 j t := by
  induction u, htu using Nat.le_induction with
  | base => exact le_rfl
  | succ u hu ih =>
    exact (hx0.1 j hj u (le_trans ht hu)).trans ih

lemma never_feasible {x0 : ℕ → ℕ → ℝ} (hx0 : S.WellFormed x0) : S.Feasible x0 (neverOrder x0) := by
  refine Filter.Eventually.of_forall fun ω k i hi => ⟨?_, ?_⟩
  · rw [pos_never, Y_never]
    by_cases hk : 1 ≤ k
    · rw [if_pos hk]
    · have : k = 0 := by omega
      subst this; simp
  · intro j hj
    rw [Y_never, pos_never]
    have hjm := (S.mem_P_iff i j).mp hj
    have hw := hx0.2 i hi j hj 1 le_rfl
    split_ifs with hl
    · have := S.x0_anti hx0 hjm.1 (t := 1) (u := 1 + S.l j) le_rfl (by omega)
      linarith
    · have := S.x0_anti hx0 hjm.1 (t := S.l j - k) (u := 1 + S.l j) (by omega) (by omega)
      linarith

lemma never_bounds [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) (x0 : ℕ → ℕ → ℝ) :
    ∃ P Q : ℝ, 0 ≤ P ∧ 0 ≤ Q ∧
      (∀ ω k, |S.stageCost (neverOrder x0) ω k| ≤ P + Q * Sk k ω) ∧
      (∀ e : ℝ, 0 ≤ e → ∀ ω k,
        |S.α ^ S.l 1 * (S.p + S.H1) * (S.backlog (Y (neverOrder x0) ω k 1 + e) -
          S.backlog (Y (neverOrder x0) ω k 1))| ≤ P + Q * Sk k ω) := by
  obtain ⟨M, hM0, hM⟩ := S.backlog_bound hν
  set κ : ℝ := S.α ^ S.l 1 * (S.p + S.H1) with hκ
  set c : ℕ → ℝ := fun j => S.α ^ S.l j * S.h j with hc
  refine ⟨∑ j ∈ S.items, |c j| * |x0 j 1| + |κ| * (M + |x0 1 1|), ∑ j ∈ S.items, |c j| + |κ|,
    by positivity, by positivity, ?_, ?_⟩
  · intro ω k
    have hD : |∑ r ∈ Finset.range k, ω r| ≤ Sk k ω := Finset.abs_sum_le_sum_abs _ _
    have hS0 : 0 ≤ Sk k ω := Finset.sum_nonneg fun r _ => abs_nonneg _
    unfold Model.stageCost
    simp only [Y_never]
    set D := ∑ r ∈ Finset.range k, ω r with hDdef
    have h1 : |∑ j ∈ S.items, S.α ^ S.l j * S.h j * (x0 j 1 - D)| ≤
        ∑ j ∈ S.items, |c j| * |x0 j 1| + (∑ j ∈ S.items, |c j|) * Sk k ω := by
      calc _ ≤ ∑ j ∈ S.items, |S.α ^ S.l j * S.h j * (x0 j 1 - D)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ S.items, (|c j| * |x0 j 1| + |c j| * Sk k ω) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have : |x0 j 1 - D| ≤ |x0 j 1| + Sk k ω := (abs_sub _ _).trans (by linarith)
            have h2 : 0 ≤ |c j| := abs_nonneg _
            calc |S.α ^ S.l j * S.h j| * |x0 j 1 - D| ≤ |c j| * (|x0 j 1| + Sk k ω) :=
                  mul_le_mul_of_nonneg_left this h2
              _ = _ := by ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul]
    have h3 : |κ * S.backlog (x0 1 1 - D)| ≤ |κ| * (M + |x0 1 1|) + |κ| * Sk k ω := by
      rw [abs_mul, abs_of_nonneg (S.backlog_nonneg _)]
      have := hM (x0 1 1 - D)
      have h4 : |x0 1 1 - D| ≤ |x0 1 1| + Sk k ω := (abs_sub _ _).trans (by linarith)
      calc |κ| * S.backlog (x0 1 1 - D) ≤ |κ| * (M + |x0 1 1| + Sk k ω) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ = _ := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h3
      _ = _ := by ring
  · intro e he ω k
    have hD : |∑ r ∈ Finset.range k, ω r| ≤ Sk k ω := Finset.abs_sum_le_sum_abs _ _
    have hS0 : 0 ≤ Sk k ω := Finset.sum_nonneg fun r _ => abs_nonneg _
    simp only [Y_never]
    set D := ∑ r ∈ Finset.range k, ω r with hDdef
    have hb1 := S.backlog_anti hν (x0 1 1 - D) e he
    have hb0 := S.backlog_nonneg (x0 1 1 - D + e)
    have hb2 := S.backlog_nonneg (x0 1 1 - D)
    have h4 : |x0 1 1 - D| ≤ |x0 1 1| + Sk k ω := (abs_sub _ _).trans (by linarith)
    have hbd := hM (x0 1 1 - D)
    have h5 : |S.backlog (x0 1 1 - D + e) - S.backlog (x0 1 1 - D)| ≤ M + |x0 1 1| + Sk k ω := by
      rw [abs_le]; constructor <;> linarith
    rw [abs_mul]
    have hP : 0 ≤ ∑ j ∈ S.items, |c j| * |x0 j 1| := Finset.sum_nonneg fun j _ => by positivity
    have hQ : 0 ≤ ∑ j ∈ S.items, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    calc |κ| * |S.backlog (x0 1 1 - D + e) - S.backlog (x0 1 1 - D)|
        ≤ |κ| * (M + |x0 1 1| + Sk k ω) := mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
      _ ≤ _ := by nlinarith [abs_nonneg κ, hP, hQ, hS0]

theorem perturb_never_cost [IsProbabilityMeasure S.ν] (hν : Integrable id S.ν) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hα0 : 0 < S.α) (hα1 : S.α < 1) {i : ℕ} (hi : i ∈ S.items)
    {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hb1 : ∀ ω k, |S.stageCost (neverOrder x0) ω k| ≤ P + Q * Sk k ω)
    (hb2 : ∀ e : ℝ, 0 ≤ e → ∀ ω k,
        |S.α ^ S.l 1 * (S.p + S.H1) * (S.backlog (Y (neverOrder x0) ω k 1 + e) -
          S.backlog (Y (neverOrder x0) ω k 1))| ≤ P + Q * Sk k ω)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ r : ℝ, S.cost (S.perturb (neverOrder x0) i δ) = (r : EReal) ∧
      r ≤ (∫ ω, ∑' k, S.α ^ k * S.stageCost (neverOrder x0) ω k ∂S.demandSeq) +
        δ * S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i *
          (S.h i + ∑ k ∈ S.B i,
            S.h k * S.α ^ (-((S.M (S.succ k) : ℤ) - (S.M (S.succ i) : ℤ)))) / (1 - S.α) +
        ∫ ω, ∑' k, S.α ^ k * (P + Q * Sk k ω) ∂S.demandSeq := by
  haveI := S.demand_prob
  set π0 := neverOrder x0 with hπ0
  have hπm : IsMeasurablePolicy π0 := never_measurable x0
  set μ := S.demandSeq with hμ
  set g : ℕ → (ℕ → ℝ) → ℝ := fun k ω => S.α ^ k * S.stageCost π0 ω k with hg
  have hgm : ∀ k, Measurable (g k) := fun k =>
    measurable_const.mul (S.stageCost_measurable π0 hπm k)
  have habs : AbsFin μ g := S.absFin_of_bound hν hP hQ hα0 hα1 hgm (fun k ω => by
    rw [hg]; simp only []
    rw [abs_mul, abs_of_pos (pow_pos hα0 k)]
    exact mul_le_mul_of_nonneg_left (hb1 ω k) (pow_nonneg hα0.le k))
  set u : ℕ → (ℕ → ℝ) → ℝ := fun k ω => S.α ^ k * (P + Q * Sk k ω) with hu
  have hum : ∀ k, Measurable (u k) := fun k =>
    measurable_const.mul (measurable_const.add (measurable_const.mul (Sk_measurable k)))
  have hunn : ∀ k ω, 0 ≤ u k ω := fun k ω => by
    have : 0 ≤ Sk k ω := Finset.sum_nonneg fun r _ => abs_nonneg _
    simp only [hu]; positivity
  have habsu : AbsFin μ u := S.absFin_of_bound hν hP hQ hα0 hα1 hum (fun k ω => by
    rw [abs_of_nonneg (hunn k ω)])
  set c : ℕ → ℝ := fun j => S.α ^ S.l j * S.h j with hc
  set d1 : ℕ → (ℕ → ℝ) → ℝ := fun k _ => S.α ^ k * ∑ j ∈ S.items, c j * S.ext i δ j k with hd1
  have hd1m : ∀ k, Measurable (d1 k) := fun k => measurable_const
  have hdS : HasSum (fun k : ℕ => S.α ^ k * ∑ j ∈ S.items, c j * S.ext i δ j k)
      (∑ j ∈ S.items, c j *
        (if j ∈ insert i (S.B i) then δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α) else 0)) := by
    have := hasSum_sum (s := S.items) (fun j _ => (S.ext_hasSum i (δ := δ) j hα0.le hα1).mul_left (c j))
    have e : (fun k : ℕ => S.α ^ k * ∑ j ∈ S.items, c j * S.ext i δ j k) =
        fun b => ∑ i_1 ∈ S.items, c i_1 * (S.α ^ b * S.ext i δ i_1 b) := by
      funext k
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]; exact this
  have habsd1 : AbsFin μ d1 := by
    unfold AbsFin
    simp only [hd1, lintegral_const, measure_univ, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => abs_nonneg _) hdS.summable.abs]
    exact ENNReal.ofReal_ne_top
  set d2 : ℕ → (ℕ → ℝ) → ℝ := fun k ω => S.α ^ k * (S.α ^ S.l 1 * (S.p + S.H1) *
    (S.backlog (Y π0 ω k 1 + S.ext i δ 1 k) - S.backlog (Y π0 ω k 1))) with hd2
  have hd2m : ∀ k, Measurable (d2 k) := fun k =>
    measurable_const.mul (measurable_const.mul
      ((S.backlog_measurable.comp ((Y_measurable π0 hπm k 1).add measurable_const)).sub
        (S.backlog_measurable.comp (Y_measurable π0 hπm k 1))))
  have hd2b : ∀ k ω, |d2 k ω| ≤ u k ω := fun k ω => by
    simp only [hd2, hu]
    rw [abs_mul, abs_of_pos (pow_pos hα0 k)]
    exact mul_le_mul_of_nonneg_left (hb2 _ (S.ext_nonneg i hδ 1 k) ω k) (pow_nonneg hα0.le k)
  have habsd2 : AbsFin μ d2 := S.absFin_of_bound hν hP hQ hα0 hα1 hd2m (fun k ω => hd2b k ω)
  have hstage : ∀ k ω, S.α ^ k * S.stageCost (S.perturb π0 i δ) ω k =
      (g k ω + d1 k ω) + d2 k ω := by
    intro k ω
    rw [S.stageCost_perturb_gen]
    simp only [hg, hd1, hd2, hc]
    rw [mul_add, mul_add]
  have hg1m : ∀ k, Measurable (fun ω => g k ω + d1 k ω) := fun k => (hgm k).add (hd1m k)
  have hg2m : ∀ k, Measurable (fun ω => (g k ω + d1 k ω) + d2 k ω) := fun k =>
    (hg1m k).add (hd2m k)
  have habs1 := absFin_add hgm hd1m habs habsd1
  have habs2 := absFin_add hg1m hd2m habs1 habsd2
  have hcost' : S.cost (S.perturb π0 i δ) =
      (((∫⁻ ω, ∑' k, ENNReal.ofReal ((g k ω + d1 k ω) + d2 k ω) ∂μ : ENNReal) : EReal) -
      ((∫⁻ ω, ∑' k, ENNReal.ofReal (- ((g k ω + d1 k ω) + d2 k ω)) ∂μ : ENNReal) : EReal)) := by
    unfold Model.cost
    simp only [hstage]
    rfl
  refine ⟨∫ ω, ∑' k, ((g k ω + d1 k ω) + d2 k ω) ∂μ, ?_, ?_⟩
  · rw [hcost']; exact (cost_eq_integral hg2m habs2).2
  · rw [integral_tsum_add hg1m hd2m habs1 habsd2, integral_tsum_add hgm hd1m habs habsd1]
    have hdint : ∫ ω, ∑' k, d1 k ω ∂μ = ∑ j ∈ S.items, c j *
        (if j ∈ insert i (S.B i) then δ * S.α ^ (S.Mmax i - S.M j) / (1 - S.α) else 0) := by
      simp only [hd1]
      rw [hdS.tsum_eq]
      simp
    rw [hdint, S.Dval_eq hT hα0.ne' hi δ]
    have hle : ∫ ω, ∑' k, d2 k ω ∂μ ≤ ∫ ω, ∑' k, u k ω ∂μ := by
      refine integral_mono_ae (cost_eq_integral hd2m habsd2).1 (cost_eq_integral hum habsu).1 ?_
      filter_upwards [ae_summable hd2m habsd2, ae_summable hum habsu] with ω h1 h2
      exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hd2b k ω)) h1 h2
    linarith

lemma X_eq (hα : S.α ≠ 0) (i : ℕ) :
    S.α ^ (S.M (S.succ i)) * S.echelonSum i =
      S.h i + ∑ k ∈ S.B i, S.h k * S.α ^ (-((S.M (S.succ k) : ℤ) - (S.M (S.succ i) : ℤ))) := by
  have key : ∀ m : ℕ, S.α ^ (S.M (S.succ i)) * S.α ^ (-(m : ℤ)) =
      S.α ^ (-((m : ℤ) - (S.M (S.succ i) : ℤ))) := by
    intro m
    rw [← zpow_natCast, ← zpow_add₀ hα]
    congr 1; ring
  unfold Model.echelonSum
  rw [mul_add, Finset.mul_sum]
  congr 1
  · rw [show S.α ^ (S.M (S.succ i)) * (S.h i * S.α ^ (-(S.M (S.succ i) : ℤ))) =
        S.h i * (S.α ^ (S.M (S.succ i)) * S.α ^ (-(S.M (S.succ i) : ℤ))) by ring, key]
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show S.α ^ (S.M (S.succ i)) * (S.h k * S.α ^ (-(S.M (S.succ k) : ℤ))) =
        S.h k * (S.α ^ (S.M (S.succ i)) * S.α ^ (-(S.M (S.succ k) : ℤ))) by ring, key]

theorem goal_core [IsProbabilityMeasure S.ν] (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ S.items) (hneg : S.echelonSum i < 0) (C : ℝ) :
    ∃ π : RoslingAssembly.SeriesEquiv.Policy, IsMeasurablePolicy π ∧ S.Feasible x0 π ∧
      ∃ r : ℝ, S.cost π = (r : EReal) ∧ r < C := by
  have hν : Integrable id S.ν := hD.2.2.1
  obtain ⟨P, Q, hP, hQ, hb1, hb2⟩ := S.never_bounds hν x0
  set J0 := ∫ ω, ∑' k, S.α ^ k * S.stageCost (neverOrder x0) ω k ∂S.demandSeq with hJ0
  set B0 := ∫ ω, ∑' k, S.α ^ k * (P + Q * Sk k ω) ∂S.demandSeq with hB0
  set X := S.h i + ∑ k ∈ S.B i,
    S.h k * S.α ^ (-((S.M (S.succ k) : ℤ) - (S.M (S.succ i) : ℤ))) with hX
  have hXneg : X < 0 := by
    have hXe : X = S.α ^ (S.M (S.succ i)) * S.echelonSum i := (S.X_eq hα0.ne' i).symm
    rw [hXe]
    exact mul_neg_of_pos_of_neg (pow_pos hα0 _) hneg
  set Kc := S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i * X / (1 - S.α) with hKc
  have hKneg : Kc < 0 := by
    have h1 : 0 < 1 - S.α := by linarith
    have h2 : 0 < S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i := by positivity
    rw [hKc]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h2 hXneg) h1
  set δ : ℝ := max 0 ((J0 + B0 - C + 1) / (-Kc)) with hδ
  have hδ0 : 0 ≤ δ := le_max_left _ _
  have hδ1 : (J0 + B0 - C + 1) / (-Kc) ≤ δ := le_max_right _ _
  refine ⟨S.perturb (neverOrder x0) i δ, (S.perturbation_feasible_core x0 hT i hi δ hδ0 _
    (never_measurable x0) (S.never_feasible hx0)).1,
    (S.perturbation_feasible_core x0 hT i hi δ hδ0 _
    (never_measurable x0) (S.never_feasible hx0)).2, ?_⟩
  obtain ⟨r, hr1, hr2⟩ := S.perturb_never_cost hν x0 hT hα0 hα1 hi hP hQ hb1 hb2 δ hδ0
  refine ⟨r, hr1, ?_⟩
  have e1 : δ * S.α ^ (S.Mmax i - S.M i) * S.α ^ S.l i * X / (1 - S.α) = δ * Kc := by
    rw [hKc]; ring
  rw [e1] at hr2
  have h3 : (J0 + B0 - C + 1) ≤ δ * (-Kc) := by
    have := (div_le_iff₀ (neg_pos.mpr hKneg)).mp hδ1
    exact this
  linarith
end Model
end RoslingAssembly.Unbounded

open RoslingAssembly.Unbounded
open MeasureTheory

theorem solution (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ S.items) (hneg : S.echelonSum i < 0) :
    ∀ C : ℝ, ∃ π : RoslingAssembly.SeriesEquiv.Policy, IsMeasurablePolicy π ∧ S.Feasible x0 π ∧
      ∃ r : ℝ, S.cost π = (r : EReal) ∧ r < C := by
  intro C; exact S.goal_core x0 hT hD hα0 hα1 hx0 i hi hneg C
