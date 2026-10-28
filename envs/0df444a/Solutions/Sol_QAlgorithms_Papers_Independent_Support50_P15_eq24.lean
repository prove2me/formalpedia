-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P15.eq24
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:24:27.177977+00:00
-- url     : https://prove2.me/submissions/2afb4176-a91d-441e-a66f-323d0262d1c6

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15
open Matrix
open scoped Matrix.Norms.L2Operator

namespace X5TE
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P15

variable {d : ℕ}

lemma tr_cfc {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian)
    (f : ℝ → ℝ) : (cfc f h).trace = ∑ i, ((f (hh.eigenvalues i) : ℝ) : ℂ) := by
  rw [hh.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rfl

lemma smul_eq_cfc {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) :
    (-((s : ℂ)⁻¹) • h) = cfc (fun x : ℝ => -s⁻¹ * x) h := by
  rw [cfc_const_mul (-s⁻¹) (fun x : ℝ => x) h, cfc_id' ℝ h]
  rw [← Complex.coe_smul]; push_cast; rfl

lemma exp_eq {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) :
    NormedSpace.exp (-((s : ℂ)⁻¹) • h) = cfc (fun x : ℝ => Real.exp (-s⁻¹ * x)) h := by
  rw [smul_eq_cfc hh s, ← CFC.real_exp_eq_normedSpace_exp, ← cfc_comp' Real.exp (fun x : ℝ => -s⁻¹ * x) h]

/-- the partition function -/
noncomputable def Z {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) : ℝ :=
  ∑ i, Real.exp (-s⁻¹ * hh.eigenvalues i)

lemma Z_pos (hd : 0 < d) {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) : 0 < Z hh s := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma thermal_eq {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) :
    thermalFinite h s = cfc (fun x : ℝ => Real.exp (-s⁻¹ * x) / Z hh s) h := by
  unfold thermalFinite gibbsState
  rw [exp_eq hh s, tr_cfc hh]
  have : (fun x : ℝ => Real.exp (-s⁻¹ * x) / Z hh s) = fun x => (Z hh s)⁻¹ * Real.exp (-s⁻¹ * x) := by
    ext x; ring
  rw [this, cfc_const_mul _ _ h (h.finite_real_spectrum.continuousOn _), ← Complex.ofReal_sum,
    ← Complex.coe_smul]
  unfold Z; push_cast; rfl

lemma tr_thermal_mul {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) (g : ℝ → ℝ) :
    (thermalFinite h s * cfc g h).trace.re =
      ∑ i, Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s * g (hh.eigenvalues i) := by
  rw [thermal_eq hh s, ← cfc_mul _ _ h (h.finite_real_spectrum.continuousOn _)
    (h.finite_real_spectrum.continuousOn _), tr_cfc hh, ← Complex.ofReal_sum, Complex.ofReal_re]

lemma csmul_eq_cfc {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (c : ℝ) :
    ((c : ℂ) • h) = cfc (fun x : ℝ => c * x) h := by
  rw [cfc_const_mul c (fun x : ℝ => x) h, cfc_id' ℝ h hh.isSelfAdjoint, Complex.coe_smul]

lemma energy_eq {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) :
    thermalExpectedEnergy h s = ∑ i, Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s * hh.eigenvalues i := by
  unfold thermalExpectedEnergy
  rw [Matrix.trace_mul_comm]
  have := tr_thermal_mul hh s (fun x => x)
  rw [cfc_id' ℝ h hh.isSelfAdjoint] at this
  exact this

lemma var_eq {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s c : ℝ) :
    stateObservableVariance (thermalFinite h s) ((c : ℂ) • h) =
      (∑ i, Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s * (c * hh.eigenvalues i) ^ 2) -
      (∑ i, Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s * (c * hh.eigenvalues i)) ^ 2 := by
  unfold stateObservableVariance
  rw [csmul_eq_cfc hh, ← cfc_pow (fun x : ℝ => c * x) 2 h (h.finite_real_spectrum.continuousOn _),
    tr_thermal_mul hh s, tr_thermal_mul hh s]

lemma surprisal_eq {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) :
    surprisalVariance (thermalFinite h s) =
      (∑ i, (Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s) *
        Real.log (Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s) ^ 2) -
      (∑ i, (Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s) *
        Real.log (Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s)) ^ 2 := by
  unfold surprisalVariance QAlgorithms.Papers.Independent.Information100.P56.entropy
  rw [thermal_eq hh s,
    ← cfc_comp' (fun x : ℝ => x * Real.log x ^ 2) (fun x : ℝ => Real.exp (-s⁻¹ * x) / Z hh s) h
      ((Set.toFinite _).continuousOn _) (h.finite_real_spectrum.continuousOn _),
    ← cfc_comp' (fun x : ℝ => x * Real.log x) (fun x : ℝ => Real.exp (-s⁻¹ * x) / Z hh s) h
      ((Set.toFinite _).continuousOn _) (h.finite_real_spectrum.continuousOn _),
    tr_cfc hh, tr_cfc hh, ← Complex.ofReal_sum, ← Complex.ofReal_sum, Complex.ofReal_re, Complex.ofReal_re]
  simp only [neg_sq]

end X5TE

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace X5TE
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P15

variable {d : ℕ}

lemma var_alg {ι : Type*} (s : Finset ι) (p e : ι → ℝ) (hp : ∑ i ∈ s, p i = 1) (a L : ℝ) :
    (∑ i ∈ s, p i * (a * e i + L) ^ 2) - (∑ i ∈ s, p i * (a * e i + L)) ^ 2 =
      a ^ 2 * ((∑ i ∈ s, p i * e i ^ 2) - (∑ i ∈ s, p i * e i) ^ 2) := by
  have h1 : ∑ i ∈ s, p i * (a * e i + L) ^ 2 =
      a ^ 2 * ∑ i ∈ s, p i * e i ^ 2 + 2 * a * L * ∑ i ∈ s, p i * e i + L ^ 2 * ∑ i ∈ s, p i := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i ∈ s, p i * (a * e i + L) = a * ∑ i ∈ s, p i * e i + L * ∑ i ∈ s, p i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, hp]; ring

lemma sum_p (hd : 0 < d) {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) :
    ∑ i, Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s = 1 := by
  rw [← Finset.sum_div]; exact div_self (Z_pos hd hh s).ne'

lemma log_p (hd : 0 < d) {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (s : ℝ) (i : Fin d) :
    Real.log (Real.exp (-s⁻¹ * hh.eigenvalues i) / Z hh s) = -(s⁻¹ * hh.eigenvalues i + Real.log (Z hh s)) := by
  rw [Real.log_div (Real.exp_pos _).ne' (Z_pos hd hh s).ne', Real.log_exp]; ring

/-- the common value -/
noncomputable def V {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (t : ℝ) : ℝ :=
  (t ^ 2)⁻¹ * ((∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) / Z hh t * hh.eigenvalues i ^ 2) -
    (∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) / Z hh t * hh.eigenvalues i) ^ 2)

lemma var_c (hd : 0 < d) {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (t c : ℝ) (ht : t ≠ 0) :
    stateObservableVariance (thermalFinite h t) ((c : ℂ) • h) = c ^ 2 * (t ^ 2 * V hh t) := by
  rw [var_eq hh t c]
  have := var_alg Finset.univ (fun i => Real.exp (-t⁻¹ * hh.eigenvalues i) / Z hh t) hh.eigenvalues
    (sum_p hd hh t) c 0
  simp only [add_zero] at this
  rw [this]
  unfold V; field_simp

lemma surprisal_V (hd : 0 < d) {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (t : ℝ) (ht : t ≠ 0) :
    surprisalVariance (thermalFinite h t) = V hh t := by
  rw [surprisal_eq hh t]
  simp only [log_p hd hh t, neg_sq, mul_neg, Finset.sum_neg_distrib]
  have := var_alg Finset.univ (fun i => Real.exp (-t⁻¹ * hh.eigenvalues i) / Z hh t) hh.eigenvalues
    (sum_p hd hh t) t⁻¹ (Real.log (Z hh t))
  rw [this]; unfold V; rw [inv_pow]

lemma hasDeriv (hd : 0 < d) {h : Matrix (Fin d) (Fin d) ℂ} (hh : h.IsHermitian) (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (thermalExpectedEnergy h) (V hh t) t := by
  have hE : thermalExpectedEnergy h = fun s =>
      (∑ i, hh.eigenvalues i * Real.exp (-s⁻¹ * hh.eigenvalues i)) / Z hh s := by
    funext s; rw [energy_eq hh s, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hw : ∀ x : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-s⁻¹ * x))
      (Real.exp (-t⁻¹ * x) * ((t ^ 2)⁻¹ * x)) t := by
    intro x
    have h0 : HasDerivAt (fun s : ℝ => -s⁻¹ * x) ((t ^ 2)⁻¹ * x) t := by
      have := (hasDerivAt_inv ht).const_mul (-x)
      have e : (fun s : ℝ => -s⁻¹ * x) = fun y => -x * y⁻¹ := by funext s; ring
      rw [e]; exact this.congr_deriv (by ring)
    exact h0.exp
  have hZ : HasDerivAt (fun s => Z hh s)
      (∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) * ((t ^ 2)⁻¹ * hh.eigenvalues i)) t := by
    unfold Z; exact HasDerivAt.fun_sum fun i _ => hw _
  have hN : HasDerivAt (fun s => ∑ i, hh.eigenvalues i * Real.exp (-s⁻¹ * hh.eigenvalues i))
      (∑ i, hh.eigenvalues i * (Real.exp (-t⁻¹ * hh.eigenvalues i) * ((t ^ 2)⁻¹ * hh.eigenvalues i))) t :=
    HasDerivAt.fun_sum fun i _ => (hw _).const_mul _
  rw [hE]
  refine (hN.div hZ (Z_pos hd hh t).ne').congr_deriv ?_
  unfold V
  have hZp := (Z_pos hd hh t).ne'
  have s1 : ∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) / Z hh t * hh.eigenvalues i ^ 2 =
      (∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) * hh.eigenvalues i ^ 2) / Z hh t := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have s2 : ∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) / Z hh t * hh.eigenvalues i =
      (∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) * hh.eigenvalues i) / Z hh t := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [s1, s2]
  unfold Z at *
  have e1 : ∑ i, hh.eigenvalues i * (Real.exp (-t⁻¹ * hh.eigenvalues i) * ((t ^ 2)⁻¹ * hh.eigenvalues i)) =
      (t ^ 2)⁻¹ * ∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) * hh.eigenvalues i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) * ((t ^ 2)⁻¹ * hh.eigenvalues i) =
      (t ^ 2)⁻¹ * ∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) * hh.eigenvalues i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, hh.eigenvalues i * Real.exp (-t⁻¹ * hh.eigenvalues i) =
      ∑ i, Real.exp (-t⁻¹ * hh.eigenvalues i) * hh.eigenvalues i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  field_simp

lemma fullrank_part {d : ℕ} (a : EntropyState d) (ha : fullRank a.val) :
    thermalFinite (-cfc Real.log a.val) 1 = a.val := by
  have hpsd := a.property.1
  have hA := hpsd.isHermitian
  unfold thermalFinite gibbsState
  have hL : IsSelfAdjoint (cfc Real.log a.val) := cfc_predicate _ _
  simp only [Complex.ofReal_one, inv_one, neg_smul, one_smul, neg_neg]
  rw [← CFC.real_exp_eq_normedSpace_exp hL, ← cfc_comp' Real.exp Real.log a.val
    ((Set.toFinite _).continuousOn _) (a.val.finite_real_spectrum.continuousOn _)]
  have hpos : ∀ x ∈ spectrum ℝ a.val, 0 < x := by
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rcases (hpsd.eigenvalues_nonneg i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hv := hA.mulVec_eigenvectorBasis i
      rw [← h, zero_smul] at hv
      have hmem : (hA.eigenvectorBasis i).ofLp ∈ LinearMap.ker a.val.mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hv
      rw [ha, Submodule.mem_bot] at hmem
      have hn := (hA.eigenvectorBasis).orthonormal.1 i
      have : hA.eigenvectorBasis i = 0 := by
        ext j; exact congrFun hmem j
      rw [this, norm_zero] at hn
      exact zero_ne_one hn
  have hcomp : cfc (fun x => Real.exp (Real.log x)) a.val = a.val := by
    rw [cfc_congr (g := fun x => x) (fun x hx => by simp [Real.exp_log (hpos x hx)])]
    exact cfc_id' ℝ a.val hA.isSelfAdjoint
  rw [hcomp, a.property.2, inv_one, one_smul]

end X5TE

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

theorem solution {d : ℕ} (hd : 0 < d) (h : Matrix (Fin d) (Fin d) ℂ)
    (hh : h.IsHermitian) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (thermalExpectedEnergy h) (stateObservableVariance (thermalFinite h t) (((t : ℂ)⁻¹) • h)) t ∧
    deriv (thermalExpectedEnergy h) t = stateObservableVariance (thermalFinite h t) (((t : ℂ)⁻¹) • h) ∧
    deriv (thermalExpectedEnergy h) t = stateObservableVariance (thermalFinite h t) h / t ^ 2 ∧
    deriv (thermalExpectedEnergy h) t = surprisalVariance (thermalFinite h t) ∧
    (∀ a : EntropyState d, fullRank a.val → thermalFinite (-cfc Real.log a.val) 1 = a.val) := by
  have hV1 : stateObservableVariance (thermalFinite h t) (((t : ℂ)⁻¹) • h) = X5TE.V hh t := by
    rw [← Complex.ofReal_inv, X5TE.var_c hd hh t t⁻¹ ht.ne']
    field_simp
  have hV2 : stateObservableVariance (thermalFinite h t) h / t ^ 2 = X5TE.V hh t := by
    have := X5TE.var_c hd hh t 1 ht.ne'
    simp only [Complex.ofReal_one, one_smul, one_pow, one_mul] at this
    rw [this]; field_simp
  have hD := X5TE.hasDeriv hd hh t ht.ne'
  refine ⟨hV1 ▸ hD, hV1 ▸ hD.deriv, hV2 ▸ hD.deriv, ?_, fun a ha => X5TE.fullrank_part a ha⟩
  rw [hD.deriv, X5TE.surprisal_V hd hh t ht.ne']

end
