-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.minimumAt_attained
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-29T15:51:55.762551+00:00
-- url     : https://prove2.me/submissions/ec24e440-2e2d-4d4d-8de9-9a95e9452f60

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

section PinHelpers

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Double-sum formula for the trace of a product of two unitarily diagonalized matrices. -/
theorem pin_trace_conj_mul (U V : Matrix.unitaryGroup n ℂ) (F G : n → ℝ) :
    ((V : Matrix n n ℂ) * Matrix.diagonal (fun i => (F i : ℂ)) * star (V : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (G j : ℂ)) * star (U : Matrix n n ℂ))).trace
      = ∑ i, ∑ j, ((F i * G j * Complex.normSq ((star (V : Matrix n n ℂ) * U) i j) : ℝ) : ℂ) := by
  set W : Matrix n n ℂ := star (V : Matrix n n ℂ) * U with hW
  have hstar : star W = star (U : Matrix n n ℂ) * V := by
    simp [hW, StarMul.star_mul]
  have key : ((V : Matrix n n ℂ) * Matrix.diagonal (fun i => (F i : ℂ)) * star (V : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (G j : ℂ)) * star (U : Matrix n n ℂ))).trace
      = (Matrix.diagonal (fun i => (F i : ℂ)) * W * Matrix.diagonal (fun j => (G j : ℂ)) *
          star W).trace := by
    rw [hstar, hW]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- Rows of the overlap probabilities of two unitaries sum to one. -/
theorem pin_row_sum (U V : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, Complex.normSq ((star (V : Matrix n n ℂ) * U) i j) = 1 := by
  set W : Matrix n n ℂ := star (V : Matrix n n ℂ) * U with hW
  have hWu : W ∈ Matrix.unitaryGroup n ℂ := by
    rw [hW]
    exact (star V * U).2
  have h1 : (W * star W) i i = 1 := by
    rw [Matrix.mem_unitaryGroup_iff.mp hWu]; simp
  have h2 : (W * star W) i i = ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.mul_conj]; rfl
  exact_mod_cast h2.symm.trans h1

/-- Scalar estimate for `h(b,a) = b log b - b log a - b + a`. -/
theorem pin_scalar {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) :
    0 ≤ b * Real.log b - b * Real.log a - b + a ∧
      b * Real.log b - b * Real.log a - b + a ≤ (b - a) ^ 2 / c := by
  have ha0 : 0 < a := lt_of_lt_of_le hc ha
  rcases hb.lt_or_eq with hb | hb
  · constructor
    · have := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
      rw [Real.log_div ha0.ne' hb.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this hb.le
      have h3 : b * (a / b - 1) = a - b := by field_simp
      nlinarith
    · have := Real.log_le_sub_one_of_pos (div_pos hb ha0)
      rw [Real.log_div hb.ne' ha0.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this hb.le
      have h3 : b * (b / a - 1) - b + a = (b - a) ^ 2 / a := by field_simp; ring
      have h4 : (b - a) ^ 2 / a ≤ (b - a) ^ 2 / c :=
        div_le_div_of_nonneg_left (sq_nonneg _) hc ha
      nlinarith
  · subst hb
    simp only [Real.log_zero, mul_zero, zero_mul, sub_zero, zero_sub, zero_add]
    refine ⟨ha0.le, ?_⟩
    rw [neg_sq, le_div_iff₀ hc]
    nlinarith

/-- Overlap probabilities between the eigenbases of two Hermitian matrices. -/
noncomputable def pin_P {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq ((star (hB.eigenvectorUnitary : Matrix n n ℂ) * hA.eigenvectorUnitary) i j)

theorem pin_P_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ pin_P hA hB i j := Complex.normSq_nonneg _

theorem pin_P_row {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    ∑ j, pin_P hA hB i j = 1 := pin_row_sum _ _ i

theorem pin_trace_cfc {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f B * cfc g A).trace = ((∑ i, ∑ j, f (hB.eigenvalues i) * g (hA.eigenvalues j) *
      pin_P hA hB i j : ℝ) : ℂ) := by
  rw [hB.cfc_eq, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have := pin_trace_conj_mul hA.eigenvectorUnitary hB.eigenvectorUnitary
    (f ∘ hB.eigenvalues) (g ∘ hA.eigenvalues)
  push_cast at this ⊢
  convert this using 1 <;> rfl

end PinHelpers
namespace PinAux

/-- The finite Umegaki expression. -/
def Dfin {d : ℕ} (rho sigma : Mat d) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) rho - rho * cfc Real.log sigma).trace.re

theorem relEnt_of_supp {d : ℕ} {rho sigma : Mat d}
    (h : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma) :
    relativeEntropy rho sigma = (Dfin rho sigma : EReal) := by
  simp only [relativeEntropy, if_pos h, Dfin]

theorem supp_of_posDef {d : ℕ} (rho : Mat d) {sigma : Mat d} (hs : sigma.PosDef) :
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma := by
  intro v hv
  have hv' : sigma *ᵥ v = 0 := hv
  by_contra hne
  have h0 : v ≠ 0 := by
    rintro rfl; exact hne (by simp)
  have := hs.dotProduct_mulVec_pos h0
  rw [hv'] at this
  simp at this

end PinAux
namespace PinAux
theorem supp_weight {d : ℕ} {rho sigma : Mat d} (hr : rho.PosSemidef) (hs : sigma.PosSemidef)
    (h : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma) (i j : Fin d)
    (hj : hs.isHermitian.eigenvalues j = 0) :
    hr.isHermitian.eigenvalues i * pin_P hs.isHermitian hr.isHermitian i j = 0 := by
  set g : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  have hfin := Matrix.finite_real_spectrum (A := sigma)
  have hsa : IsSelfAdjoint sigma := hs.isHermitian
  have hrsa : IsSelfAdjoint rho := hr.isHermitian
  have hsP : sigma * cfc g sigma = 0 := by
    have : cfc (fun x => x * g x) sigma = 0 := by
      rw [show (fun x => x * g x) = fun _ => (0 : ℝ) by
        funext x; by_cases hx : x = 0 <;> simp [g, hx]]
      exact cfc_const_zero ℝ sigma
    rw [cfc_mul (fun x : ℝ => x) g sigma (hfin.continuousOn _) (hfin.continuousOn _),
      cfc_id' ℝ sigma hsa] at this
    exact this
  have hrP : rho * cfc g sigma = 0 := by
    ext a b
    have hcol : sigma *ᵥ (cfc g sigma *ᵥ Pi.single b 1) = 0 := by
      rw [Matrix.mulVec_mulVec, hsP, Matrix.zero_mulVec]
    have hv : rho *ᵥ (cfc g sigma *ᵥ Pi.single b 1) = 0 := h hcol
    have := congrFun hv a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    simpa using this
  have htr := pin_trace_cfc hs.isHermitian hr.isHermitian (fun x => x) g
  rw [cfc_id' ℝ rho hrsa, hrP, Matrix.trace_zero] at htr
  have hsum : (∑ i, ∑ j, hr.isHermitian.eigenvalues i * g (hs.isHermitian.eigenvalues j) *
      pin_P hs.isHermitian hr.isHermitian i j) = 0 := by exact_mod_cast htr.symm
  have hnn : ∀ i j, 0 ≤ hr.isHermitian.eigenvalues i * g (hs.isHermitian.eigenvalues j) *
      pin_P hs.isHermitian hr.isHermitian i j := fun i j =>
    mul_nonneg (mul_nonneg (hr.eigenvalues_nonneg i) (by simp only [g]; split_ifs <;> norm_num))
      (pin_P_nonneg _ _ _ _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => hnn i j))).1 hsum i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 h1 j (Finset.mem_univ _)
  simpa [g, hj] using h2
end PinAux
namespace AttAux

def St (d : ℕ) : Set (Mat d) := {X | X.PosSemidef ∧ X.trace = 1}

theorem spec_sub {d : ℕ} {X : Mat d} (hX : X ∈ St d) : spectrum ℝ X ⊆ Set.Icc 0 1 := by
  obtain ⟨hp, ht⟩ := hX
  rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  refine ⟨hp.eigenvalues_nonneg i, ?_⟩
  have htr := hp.isHermitian.trace_eq_sum_eigenvalues
  rw [ht] at htr
  have hsum : ∑ j, hp.isHermitian.eigenvalues j = 1 := by
    apply Complex.ofReal_injective; rw [Complex.ofReal_sum]; simpa using htr.symm
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hp.eigenvalues_nonneg j) (Finset.mem_univ i)

def G {d : ℕ} (ε : ℝ) (p : Mat d × Mat d) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) p.1 - p.1 * cfc (fun x : ℝ => Real.log (x + ε)) p.2).trace.re

theorem G_cont {d : ℕ} {ε : ℝ} (hε : 0 < ε) : ContinuousOn (G ε) (St d ×ˢ St d) := by
  have h1 : ContinuousOn (fun p : Mat d × Mat d => cfc (fun x : ℝ => x * Real.log x) p.1)
      (St d ×ˢ St d) :=
    ContinuousOn.cfc' isCompact_Icc _ continuous_fst.continuousOn
      (fun p hp => spec_sub hp.1) (fun p hp => (hp.1.1.isHermitian : IsSelfAdjoint p.1))
      Real.continuous_mul_log.continuousOn
  have h2 : ContinuousOn (fun p : Mat d × Mat d => cfc (fun x : ℝ => Real.log (x + ε)) p.2)
      (St d ×ˢ St d) :=
    ContinuousOn.cfc' isCompact_Icc _ continuous_snd.continuousOn
      (fun p hp => spec_sub hp.2) (fun p hp => (hp.2.1.isHermitian : IsSelfAdjoint p.2))
      (by
        intro x hx
        exact ((continuous_id.add continuous_const).continuousAt.log
          (by simp; linarith [hx.1])).continuousWithinAt)
  have := (h1.sub (continuous_fst.continuousOn.mul h2))
  exact Complex.continuous_re.comp_continuousOn
    ((continuous_id.matrix_trace).comp_continuousOn this)

end AttAux
namespace AttAux

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported)

theorem G_formula {d : ℕ} {rho sigma : Mat d} (hr : rho.IsHermitian) (hs : sigma.IsHermitian)
    (ε : ℝ) :
    G ε (rho, sigma) = ∑ i, ∑ j, (hr.eigenvalues i * Real.log (hr.eigenvalues i) -
      hr.eigenvalues i * Real.log (hs.eigenvalues j + ε)) * pin_P hs hr i j := by
  have hfr := Matrix.finite_real_spectrum (A := rho)
  have hfs := Matrix.finite_real_spectrum (A := sigma)
  have hrsa : IsSelfAdjoint rho := hr
  have hssa : IsSelfAdjoint sigma := hs
  rw [G]
  dsimp only
  rw [show rho * cfc (fun x : ℝ => Real.log (x + ε)) sigma =
      cfc (fun x : ℝ => x) rho * cfc (fun x : ℝ => Real.log (x + ε)) sigma by
    rw [cfc_id' ℝ rho hrsa]]
  rw [← Matrix.mul_one (cfc (fun x : ℝ => x * Real.log x) rho), ← cfc_const_one ℝ sigma hssa]
  rw [Matrix.trace_sub, pin_trace_cfc hs hr, pin_trace_cfc hs hr,
    ← Complex.ofReal_sub, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem G_zero {d : ℕ} (rho sigma : Mat d) :
    G 0 (rho, sigma) = PinAux.Dfin rho sigma := by
  simp [G, PinAux.Dfin]

theorem supp_of_weights {d : ℕ} {rho sigma : Mat d} (hr : rho.PosSemidef) (hs : sigma.PosSemidef)
    (hw : ∀ i j, hs.isHermitian.eigenvalues j = 0 →
      hr.isHermitian.eigenvalues i * pin_P hs.isHermitian hr.isHermitian i j = 0) :
    IsSupported rho sigma := by
  set g : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  set h : ℝ → ℝ := fun x => if x = 0 then 0 else x⁻¹
  have hfin := Matrix.finite_real_spectrum (A := sigma)
  have hssa : IsSelfAdjoint sigma := hs.isHermitian
  have hrsa : IsSelfAdjoint rho := hr.isHermitian
  set Q0 := cfc g sigma
  have hQsa : Q0ᴴ = Q0 := by
    have : IsSelfAdjoint Q0 := cfc_predicate g sigma
    exact this
  have hQQ : Q0 * Q0 = Q0 := by
    rw [← cfc_mul g g sigma (hfin.continuousOn _) (hfin.continuousOn _)]
    congr 1; funext x; by_cases hx : x = 0 <;> simp [g, hx]
  have hid : Q0 + cfc h sigma * sigma = 1 := by
    have e : (fun x : ℝ => g x + h x * x) = fun _ => 1 := by
      funext x; by_cases hx : x = 0 <;> simp [g, h, hx]
    have := cfc_const_one ℝ sigma hssa
    rw [← e, cfc_add sigma g (fun x => h x * x) (hfin.continuousOn _) (hfin.continuousOn _),
      cfc_mul h (fun x : ℝ => x) sigma (hfin.continuousOn _) (hfin.continuousOn _),
      cfc_id' ℝ sigma hssa] at this
    exact this
  -- Tr(ρ Q0) = 0
  have htr0 : (rho * Q0).trace = 0 := by
    have htr := pin_trace_cfc hs.isHermitian hr.isHermitian (fun x => x) g
    rw [cfc_id' ℝ rho hrsa] at htr
    rw [htr]
    have : (∑ i, ∑ j, hr.isHermitian.eigenvalues i * g (hs.isHermitian.eigenvalues j) *
        pin_P hs.isHermitian hr.isHermitian i j) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : hs.isHermitian.eigenvalues j = 0
      · have := hw i j hj; simp only [g, hj, if_true, mul_one]; exact this
      · simp [g, hj]
    exact_mod_cast this
  set M := Q0ᴴ * rho * Q0
  have hM : M.PosSemidef := hr.conjTranspose_mul_mul_same Q0
  have hMtr : M.trace = 0 := by
    simp only [M, hQsa]
    rw [Matrix.trace_mul_cycle, hQQ, Matrix.trace_mul_comm, htr0]
  have hM0 : M = 0 := hM.trace_eq_zero_iff.1 hMtr
  intro v hv
  have hσv : sigma *ᵥ v = 0 := hv
  have hQv : Q0 *ᵥ v = v := by
    have := congrArg (fun A => A *ᵥ v) hid
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hσv, Matrix.mulVec_zero, add_zero,
      Matrix.one_mulVec] at this
    exact this
  change rho *ᵥ v = 0
  rw [← hr.dotProduct_mulVec_zero_iff]
  have : star v ⬝ᵥ M *ᵥ v = 0 := by rw [hM0]; simp
  rw [← this]
  simp only [M, ← Matrix.mulVec_mulVec, hQv]
  rw [Matrix.dotProduct_mulVec (star v) Q0ᴴ, ← Matrix.star_mulVec,
    hQv]

end AttAux
namespace AttAux

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported)

def εs (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem εs_pos (n : ℕ) : 0 < εs n := by unfold εs; positivity

theorem εs_le_one (n : ℕ) : εs n ≤ 1 := by
  unfold εs; rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem εs_anti : Antitone εs := fun n m h => by
  unfold εs
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

theorem εs_tendsto : Tendsto εs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem G_mono {d : ℕ} {rho sigma : Mat d} (hr : rho.PosSemidef) (hs : sigma.PosSemidef) :
    Monotone (fun n => G (εs n) (rho, sigma)) := by
  intro n m hnm
  simp only [G_formula hr.isHermitian hs.isHermitian]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hs0 := hs.eigenvalues_nonneg j
  have hlog : Real.log (hs.isHermitian.eigenvalues j + εs m) ≤
      Real.log (hs.isHermitian.eigenvalues j + εs n) :=
    Real.log_le_log (by linarith [εs_pos m]) (by linarith [εs_anti hnm])
  have := mul_le_mul_of_nonneg_left hlog (hr.eigenvalues_nonneg i)
  exact mul_le_mul_of_nonneg_right (by linarith) (pin_P_nonneg _ _ _ _)

theorem G_tendsto {d : ℕ} {rho sigma : Mat d} (hr : rho.PosSemidef) (hs : sigma.PosSemidef) :
    Tendsto (fun n => (G (εs n) (rho, sigma) : EReal)) atTop (𝓝 (relativeEntropy rho sigma)) := by
  by_cases hsupp : IsSupported rho sigma
  · rw [PinAux.relEnt_of_supp hsupp, ← G_zero]
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    simp only [G_formula hr.isHermitian hs.isHermitian]
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    set r := hr.isHermitian.eigenvalues i
    set s := hs.isHermitian.eigenvalues j
    set P := pin_P hs.isHermitian hr.isHermitian i j
    by_cases hs0 : s = 0
    · have hw : r * P = 0 := PinAux.supp_weight hr hs hsupp i j hs0
      have e : ∀ ε, (r * Real.log r - r * Real.log (s + ε)) * P = r * Real.log r * P := by
        intro ε
        have : r * Real.log (s + ε) * P = 0 := by
          rw [mul_right_comm, hw, zero_mul]
        linear_combination -this
      simp only [e]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun ε => (r * Real.log r - r * Real.log (s + ε)) * P) 0 := by
        have : ContinuousAt (fun ε => Real.log (s + ε)) 0 :=
          (continuous_const.add continuous_id).continuousAt.log (by simpa using hs0)
        exact (continuousAt_const.sub (continuousAt_const.mul this)).mul continuousAt_const
      exact hc.tendsto.comp εs_tendsto
  · simp only [relativeEntropy, if_neg hsupp]
    have hex : ∃ i j, hs.isHermitian.eigenvalues j = 0 ∧
        hr.isHermitian.eigenvalues i * pin_P hs.isHermitian hr.isHermitian i j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hsupp (supp_of_weights hr hs hcon)
    obtain ⟨i, j, hs0, hne⟩ := hex
    set c := hr.isHermitian.eigenvalues i * pin_P hs.isHermitian hr.isHermitian i j
    have hc : 0 < c := lt_of_le_of_ne
      (mul_nonneg (hr.eigenvalues_nonneg i) (pin_P_nonneg _ _ _ _)) (Ne.symm hne)
    set B := ∑ i, ∑ j, (hr.isHermitian.eigenvalues i * Real.log (hr.isHermitian.eigenvalues i) -
      hr.isHermitian.eigenvalues i * Real.log (hs.isHermitian.eigenvalues j + 1)) *
        pin_P hs.isHermitian hr.isHermitian i j
    have hbound : ∀ n, B - c * Real.log (εs n) ≤ G (εs n) (rho, sigma) := by
      intro n
      set ε := εs n
      have hε0 := εs_pos n
      have hε1 := εs_le_one n
      rw [G_formula hr.isHermitian hs.isHermitian]
      have hdiff : G (εs n) (rho, sigma) - B = ∑ i, ∑ j,
          hr.isHermitian.eigenvalues i * pin_P hs.isHermitian hr.isHermitian i j *
            (Real.log (hs.isHermitian.eigenvalues j + 1) -
              Real.log (hs.isHermitian.eigenvalues j + ε)) := by
        rw [G_formula hr.isHermitian hs.isHermitian, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have hnn : ∀ i j, 0 ≤ hr.isHermitian.eigenvalues i * pin_P hs.isHermitian hr.isHermitian i j *
            (Real.log (hs.isHermitian.eigenvalues j + 1) -
              Real.log (hs.isHermitian.eigenvalues j + ε)) := by
        intro i j
        have hsj := hs.eigenvalues_nonneg j
        exact mul_nonneg (mul_nonneg (hr.eigenvalues_nonneg i) (pin_P_nonneg _ _ _ _))
          (sub_nonneg.2 (Real.log_le_log (by linarith) (by linarith)))
      have hsingle : -(c * Real.log ε) ≤ G (εs n) (rho, sigma) - B := by
        rw [hdiff]
        have h1 := Finset.single_le_sum (f := fun j => hr.isHermitian.eigenvalues i *
            pin_P hs.isHermitian hr.isHermitian i j *
            (Real.log (hs.isHermitian.eigenvalues j + 1) -
              Real.log (hs.isHermitian.eigenvalues j + ε))) (fun j _ => hnn i j)
          (Finset.mem_univ j)
        have h2 := Finset.single_le_sum (f := fun i => ∑ j, hr.isHermitian.eigenvalues i *
            pin_P hs.isHermitian hr.isHermitian i j *
            (Real.log (hs.isHermitian.eigenvalues j + 1) -
              Real.log (hs.isHermitian.eigenvalues j + ε)))
          (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) (Finset.mem_univ i)
        simp only [hs0, zero_add, Real.log_one, zero_sub] at h1
        have : -(c * Real.log ε) = c * -Real.log ε := by ring
        rw [this]
        exact h1.trans h2
      rw [G_formula hr.isHermitian hs.isHermitian] at hsingle
      linarith
    refine EReal.tendsto_coe_atTop.comp (tendsto_atTop_mono hbound ?_)
    have hlog : Tendsto (fun n : ℕ => Real.log (εs n)) atTop atBot :=
      Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2
        ⟨εs_tendsto, Filter.Eventually.of_forall fun n => εs_pos n⟩)
    have : Tendsto (fun n : ℕ => -(c * Real.log (εs n))) atTop atTop := by
      exact tendsto_neg_atBot_atTop.comp (hlog.const_mul_atBot hc)
    exact (tendsto_atTop_add_const_left _ B this).congr fun n => by ring

theorem relEnt_eq_iSup {d : ℕ} {rho sigma : Mat d} (hr : rho.PosSemidef) (hs : sigma.PosSemidef) :
    relativeEntropy rho sigma = ⨆ n, (G (εs n) (rho, sigma) : EReal) :=
  tendsto_nhds_unique (G_tendsto hr hs)
    (tendsto_atTop_iSup fun n m h => EReal.coe_le_coe_iff.2 (G_mono hr hs h))

theorem relEnt_lsc {d : ℕ} :
    LowerSemicontinuousOn (fun p : Mat d × Mat d => relativeEntropy p.1 p.2) (St d ×ˢ St d) := by
  have hl : LowerSemicontinuousOn (fun p : Mat d × Mat d => ⨆ n, (G (εs n) p : EReal))
      (St d ×ˢ St d) :=
    lowerSemicontinuousOn_iSup fun n =>
      (continuous_coe_real_ereal.comp_continuousOn (G_cont (εs_pos n))).lowerSemicontinuousOn
  intro p hp y hy
  simp only at hy ⊢
  have heq : ∀ q ∈ St d ×ˢ St d, relativeEntropy q.1 q.2 = ⨆ n, (G (εs n) q : EReal) :=
    fun q hq => relEnt_eq_iSup hq.1.1 hq.2.1
  rw [heq p hp] at hy
  filter_upwards [hl p hp y hy, self_mem_nhdsWithin] with q hq hqs
  rw [heq q hqs]; exact hq

end AttAux
namespace AttAux

theorem entry_le {d : ℕ} {X : Mat d} (hX : X ∈ St d) (i j : Fin d) : ‖X i j‖ ≤ 1 := by
  obtain ⟨hp, ht⟩ := hX
  have htr := hp.isHermitian.trace_eq_sum_eigenvalues
  rw [ht] at htr
  have hsum : ∑ k, hp.isHermitian.eigenvalues k = 1 := by
    apply Complex.ofReal_injective; rw [Complex.ofReal_sum]; simpa using htr.symm
  have hspec := hp.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U := hp.isHermitian.eigenvectorUnitary
  have hX : X i j = ∑ k, (U : Mat d) i k * (hp.isHermitian.eigenvalues k : ℂ) *
      star ((U : Mat d) j k) := by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_apply]
    simp [Matrix.mul_diagonal, Matrix.star_apply]
  rw [hX]
  refine (norm_sum_le _ _).trans ?_
  rw [← hsum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := entry_norm_bound_of_unitary U.2 i k
  have h2 := entry_norm_bound_of_unitary U.2 j k
  have h0 := hp.eigenvalues_nonneg k
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg h0]
  have := norm_nonneg ((U : Mat d) i k)
  have := norm_nonneg ((U : Mat d) j k)
  calc ‖(U : Mat d) i k‖ * hp.isHermitian.eigenvalues k * ‖(U : Mat d) j k‖
      ≤ 1 * hp.isHermitian.eigenvalues k * 1 := by gcongr
    _ = _ := by ring

def K (d : ℕ) : Set (Mat d) := {X | ∀ i j, ‖X i j‖ ≤ 1}

theorem K_compact {d : ℕ} : IsCompact (K d) := by
  have : K d = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    ext X
    show _ ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, X i j ∈ Metric.closedBall (0 : ℂ) 1
    simp [K]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem St_closed {d : ℕ} : IsClosed (St d) := by
  have hpsd : {X : Mat d | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ x : Fin d → ℂ, {X | 0 ≤ star x ⬝ᵥ X *ᵥ x} := by
    ext X; simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  have h1 : IsClosed {X : Mat d | X.PosSemidef} := by
    rw [hpsd]
    refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
      (isClosed_iInter fun x => isClosed_le continuous_const ?_)
    exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact h1.inter (isClosed_eq continuous_id.matrix_trace continuous_const)

def gN {d : ℕ} (N : Mat d → ℝ) (A : Mat d) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ * N (Matrix.single i j 1)

theorem N_cont {d : ℕ} {N : Mat d → ℝ} (hN : IsUINorm N) : Continuous N := by
  obtain ⟨-, hz, htri, hsm, -⟩ := hN
  have hN0 : N 0 = 0 := (hz 0).2 rfl
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Mat d), N (∑ x ∈ s, f x) ≤ ∑ x ∈ s, N (f x) := by
    intro ι s f
    classical
    induction s using Finset.induction_on with
    | empty => simp [hN0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (htri _ _).trans (by linarith)
  have hb : ∀ A, N A ≤ gN N A := by
    intro A
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    refine (hsum _ _).trans (Finset.sum_le_sum fun i _ => (hsum _ _).trans ?_)
    refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, hsm]
  have hg : Continuous (gN N) := by
    unfold gN
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((continuous_id.matrix_elem i j).norm).mul continuous_const
  have hneg : ∀ A, N (-A) = N A := by
    intro A
    have := hsm (-1) A
    simpa using this
  have hlo : ∀ A B, N A - gN N (B - A) ≤ N B := by
    intro A B
    have h1 := htri (A - B) B
    rw [sub_add_cancel] at h1
    have h2 := hb (A - B)
    have h3 : N (A - B) = N (B - A) := by rw [← hneg, neg_sub]
    have h4 := hb (B - A)
    linarith
  have hhi : ∀ A B, N B ≤ N A + gN N (B - A) := by
    intro A B
    have h1 := htri (B - A) A
    rw [sub_add_cancel] at h1
    linarith [hb (B - A)]
  refine continuous_iff_continuousAt.2 fun A => ?_
  have hgt : Tendsto (fun B => gN N (B - A)) (𝓝 A) (𝓝 0) := by
    have hc : Continuous fun B : Mat d => gN N (B - A) := hg.comp (continuous_id.sub continuous_const)
    simpa [gN] using hc.tendsto A
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub hgt) (by simpa using tendsto_const_nhds.add hgt)
    (fun B => hlo A B) (fun B => hhi A B)

def vec (d : ℕ) (a b : ℝ) : Fin d → ℂ :=
  fun i => if i.val = 0 then (a : ℂ) else if i.val = 1 then (b : ℂ) else 0

theorem vec_state {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Matrix.diagonal (vec d a b) ∈ St d := by
  refine ⟨Matrix.posSemidef_diagonal_iff.2 fun i => ?_, ?_⟩
  · unfold vec; split_ifs <;> simp [ha, hb]
  · rw [Matrix.trace_diagonal, Fintype.sum_eq_add (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩
      (by simp [Fin.ext_iff])]
    · simp [vec]; exact_mod_cast hab
    · rintro x ⟨h1, h2⟩
      simp only [vec]
      rw [if_neg (fun h => h1 (Fin.ext h)), if_neg (fun h => h2 (Fin.ext h))]

theorem vec_diff {d : ℕ} (a b : ℝ) :
    Matrix.diagonal (vec d a b) - Matrix.diagonal (vec d b a) = (((a - b : ℝ) : ℂ)) • matrixF d := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp only [vec, matrixF, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq]
    split_ifs <;> push_cast <;> ring
  · simp [Matrix.diagonal_apply_ne _ hij, matrixF]

theorem main {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T : ℝ) (hT : 0 ≤ T ∧ T ≤ N (matrixF d)) :
    ∃ rho sigma : Mat d, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      N (rho - sigma) = T ∧ relativeEntropy rho sigma = minimumAt d N T := by
  have hNc := N_cont hN
  obtain ⟨h0, hz, -, hsm, -⟩ := hN
  have hF : 0 < N (matrixF d) := by
    refine lt_of_le_of_ne (h0 _) fun h => ?_
    have h' := congrFun (congrFun ((hz _).1 h.symm) ⟨0, by omega⟩) ⟨0, by omega⟩
    simp [matrixF] at h'
  set c := T / N (matrixF d) with hc
  have hc0 : 0 ≤ c := div_nonneg hT.1 hF.le
  have hc1 : c ≤ 1 := (div_le_one hF).2 hT.2
  set S : Set (Mat d × Mat d) := St d ×ˢ St d ∩ {p | N (p.1 - p.2) = T} with hS
  have hne : S.Nonempty := by
    refine ⟨(Matrix.diagonal (vec d ((1 + c) / 2) ((1 - c) / 2)),
      Matrix.diagonal (vec d ((1 - c) / 2) ((1 + c) / 2))),
      ⟨vec_state hd (by linarith) (by linarith) (by ring),
        vec_state hd (by linarith) (by linarith) (by ring)⟩, ?_⟩
    show N (_ - _) = T
    rw [vec_diff, hsm, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have : (1 + c) / 2 - (1 - c) / 2 = c := by ring
    rw [this, hc, div_mul_cancel₀ _ hF.ne']
  have hclosed : IsClosed S :=
    (St_closed.prod St_closed).inter
      (isClosed_eq (hNc.comp (continuous_fst.sub continuous_snd)) continuous_const)
  have hcomp : IsCompact S :=
    (K_compact.prod K_compact).of_isClosed_subset hclosed
      fun p hp => ⟨entry_le hp.1.1, entry_le hp.1.2⟩
  obtain ⟨p, hp, hmin⟩ :=
    (relEnt_lsc.mono Set.inter_subset_left).exists_isMinOn hne hcomp
  refine ⟨p.1, p.2, hp.1.1, hp.1.2, hp.2, le_antisymm ?_ ?_⟩
  · refine le_sInf ?_
    rintro v ⟨r, s, hr, hs, hT', rfl⟩
    exact isMinOn_iff.1 hmin (r, s) ⟨⟨hr, hs⟩, hT'⟩
  · exact sInf_le ⟨p.1, p.2, hp.1.1, hp.1.2, hp.2, rfl⟩

end AttAux

end QAlgorithms.Papers.Independent.Gap48.P40

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T : ℝ) (hT : 0 ≤ T ∧ T ≤ N (matrixF d)) :
    ∃ rho sigma : Mat d, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      N (rho - sigma) = T ∧ relativeEntropy rho sigma = minimumAt d N T :=
  AttAux.main hd N hN T hT

end
