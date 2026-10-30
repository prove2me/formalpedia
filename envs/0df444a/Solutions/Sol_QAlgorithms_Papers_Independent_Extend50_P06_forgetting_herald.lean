-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P06.forgetting_herald
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:20:26.279351+00:00
-- url     : https://prove2.me/submissions/202869b7-7a2d-406a-8ed1-f9e79836f64d

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P06
namespace QAlgorithms.Papers.Independent.Extend50.P06

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

-- Exact accepted interfaces; no duplicate SU subtype or ambient-coordinate Haar law.

open QAlgorithms.Papers.Independent.Information100.P47 (Mat)

open QAlgorithms.Papers.Independent.Claimed50.P21 (SU HaarLaw)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P06.targetMatrixMeasurable


lemma p06s_insert_add {k d e : ℕ} (S T : TransformationProcess k d e) (C) :
    insertSlots (S + T) C = insertSlots S C + insertSlots T C := by
  ext x y
  simp [insertSlots, add_mul, Finset.sum_add_distrib]

lemma p06s_pf_add {k d e : ℕ} (S T : TransformationProcess k d e) (f : SU d → Mat e) (U : SU d) :
    pointFidelity (S + T) f U = pointFidelity S f U + pointFidelity T f U := by
  unfold pointFidelity targetChoiFidelity
  rw [p06s_insert_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re, add_div]

lemma p06s_trJJ {e : ℕ} (V : Mat e) (hV : V ∈ Matrix.specialUnitaryGroup (Fin e) ℂ) :
    Matrix.trace (transformationChoi V * transformationChoi V) = (e : ℂ) ^ 2 := by
  have hu : V ∈ Matrix.unitaryGroup (Fin e) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp hV).1
  have h1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hs : ∑ a : Fin e × Fin e, V a.2 a.1 * conj (V a.2 a.1) = (e : ℂ) := by
    have := congrArg Matrix.trace h1
    rw [Matrix.trace_one] at this
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Fintype.card_fin] at this
    rw [Fintype.sum_prod_type]
    rw [← this]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    simp [RCLike.star_def]; ring
  simp only [transformationChoi, QAlgorithms.pureDensity, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.of_apply]
  have : ∀ a b : Fin e × Fin e, (V a.2 a.1 * conj (V b.2 b.1)) * (V b.2 b.1 * conj (V a.2 a.1))
      = (V a.2 a.1 * conj (V a.2 a.1)) * (V b.2 b.1 * conj (V b.2 b.1)) := fun a b => by ring
  simp_rw [this, ← Finset.mul_sum, ← Finset.sum_mul, hs]; ring

def p06sW {k d : ℕ} (U : Mat d) (p : QueryRegister k d × QueryRegister k d) : ℂ := ∏ t, U (p.2 t) (p.1 t)

lemma p06s_slots {k d : ℕ} (U : Mat d) (p q : QueryRegister k d × QueryRegister k d) :
    unitarySlots (k := k) U p q = p06sW U p * conj (p06sW U q) := by
  simp [unitarySlots, slotProductChoi, transformationChoi, QAlgorithms.pureDensity, p06sW,
    Finset.prod_mul_distrib, map_prod]

def p06sB {k d e : ℕ} (U : Mat d) : Matrix (Fin e × Fin e) (TransformationWires k d e) ℂ :=
  Matrix.of fun x X => if X.1 = x.1 then (if X.2.2.2 = x.2 then p06sW U (X.2.1, X.2.2.1) else 0) else 0

lemma p06s_insert_eq {k d e : ℕ} (S : TransformationProcess k d e) (U : Mat d) :
    insertSlots S (unitarySlots U) = p06sB (k := k) (e := e) U * S * (p06sB (k := k) (e := e) U)ᴴ := by
  ext x y
  simp [insertSlots, Matrix.mul_apply, Matrix.conjTranspose_apply, p06sB, Fintype.sum_prod_type, p06s_slots,
    apply_ite, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ∀ i : QueryRegister k d, (∑ o, ∑ v, S (x.1, i, o, x.2) (y.1, j, v, y.2) *
      (p06sW U (i, o) * (starRingEnd ℂ) (p06sW U (j, v)))) =
      ∑ v, ∑ o, S (x.1, i, o, x.2) (y.1, j, v, y.2) *
      (p06sW U (i, o) * (starRingEnd ℂ) (p06sW U (j, v))) := fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun o _ => ?_
  ring

lemma p06s_tr_quad {e : ℕ} (A : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ) (V : Mat e) :
    Matrix.trace (A * transformationChoi V) =
      star (fun x : Fin e × Fin e => V x.2 x.1) ⬝ᵥ (A *ᵥ (fun x : Fin e × Fin e => V x.2 x.1)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, transformationChoi, QAlgorithms.pureDensity,
    Matrix.of_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma p06s_pf_nonneg {k d e : ℕ} (S : TransformationProcess k d e) (hS : S.PosSemidef)
    (f : SU d → Mat e) (U : SU d) : 0 ≤ pointFidelity S f U := by
  unfold pointFidelity targetChoiFidelity
  apply div_nonneg _ (by positivity)
  rw [p06s_insert_eq, p06s_tr_quad]
  have := (hS.mul_mul_conjTranspose_same (p06sB (k := k) (e := e) U.val)).dotProduct_mulVec_nonneg
    (fun x : Fin e × Fin e => f U x.2 x.1)
  exact (Complex.nonneg_iff.mp this).1

lemma p06s_cont {k d e : ℕ} (S : TransformationProcess k d e) :
    Continuous (fun p : Mat d × Mat e =>
      (Matrix.trace (insertSlots S (unitarySlots (k := k) p.1) * transformationChoi p.2)).re / (e:ℝ)^2) := by
  simp only [insertSlots, p06s_slots, p06sW, Matrix.trace, Matrix.diag, Matrix.mul_apply, transformationChoi,
    QAlgorithms.pureDensity, Matrix.of_apply]
  fun_prop

lemma p06s_integrable {k d e : ℕ} (H : HaarLaw d) (f : Target d e) (S : TransformationProcess k d e) :
    Integrable (fun U => pointFidelity S f.value U) H.law := by
  haveI := H.probability
  haveI : ∀ n, BorelSpace (Mat n) := fun n => ⟨rfl⟩
  haveI : ∀ n, SecondCountableTopology (Mat n) := fun n =>
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  set Φ := fun p : Mat d × Mat e =>
      (Matrix.trace (insertSlots S (unitarySlots (k := k) p.1) * transformationChoi p.2)).re / (e:ℝ)^2
  have hΦ : Continuous Φ := p06s_cont S
  have hK : ∀ n, IsCompact {A : Mat n | ∀ i j, ‖A i j‖ ≤ 1} := by
    intro n
    have : {A : Mat n | ∀ i j, ‖A i j‖ ≤ 1} =
        Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0:ℂ) 1)) := by
      ext A
      exact ⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i trivial j trivial⟩
    rw [this]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  obtain ⟨C, hC⟩ := ((hK d).prod (hK e)).exists_bound_of_continuousOn hΦ.continuousOn
  have hmeas : Measurable (fun U : SU d => ((U : Mat d), f.value U)) :=
    (continuous_subtype_val.measurable).prodMk f.measurable
  refine Integrable.of_bound (C := C) ((hΦ.measurable.comp hmeas).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun U => ?_
  have hU : (U : Mat d) ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  have hV : f.value U ∈ Matrix.unitaryGroup (Fin e) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp (f.specialUnitary U)).1
  exact hC ((U : Mat d), f.value U) ⟨fun i j => entry_norm_bound_of_unitary hU i j,
    fun i j => entry_norm_bound_of_unitary hV i j⟩

end
end QAlgorithms.Papers.Independent.Extend50.P06

open QAlgorithms.Papers.Independent.Extend50.P06
open scoped BigOperators ComplexConjugate Matrix ComplexOrder
open MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P47 (Mat)
open QAlgorithms.Papers.Independent.Claimed50.P21 (SU HaarLaw)
open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)
attribute [local instance] Classical.propDecidable
attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P06.targetMatrixMeasurable

theorem solution (d e k : ℕ) (hd : 0 < d) (he : 0 < e) (hk : 1 ≤ k)
    (H : HaarLaw d) (f : Target d e) (c : StrategyClass)
    (Ss Sf : TransformationProcess k d e) (ps : ℝ) (hps : 0 ≤ ps ∧ ps ≤ 1)
    (hs : Ss.PosSemidef) (hf : Sf.PosSemidef) (hdet : TransformationAdmissible c (Ss+Sf))
    (hexact : ∀ U : SU d, insertSlots Ss (unitarySlots U.val) = (ps : ℂ) • transformationChoi (f.value U)) :
    TransformationAdmissible c (Ss+Sf) ∧
      transformationAverage H f.value (Ss+Sf) = ps +
        (∫ U, pointFidelity Sf f.value U ∂H.law) ∧
      ps ≤ transformationAverage H f.value (Ss+Sf) := by
  haveI := H.probability
  have hpf : ∀ U, pointFidelity (Ss+Sf) f.value U = ps + pointFidelity Sf f.value U := by
    intro U
    rw [p06s_pf_add]
    congr 1
    unfold pointFidelity targetChoiFidelity
    rw [hexact U, Matrix.smul_mul, Matrix.trace_smul, p06s_trJJ _ (f.specialUnitary U)]
    have he' : (0:ℝ) < (e:ℝ)^2 := by positivity
    simp only [smul_eq_mul]
    rw [show ((ps:ℂ) * (e:ℂ)^2) = ((ps * (e:ℝ)^2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    field_simp
  have hint := p06s_integrable H f Sf
  have hav : transformationAverage H f.value (Ss+Sf) = ps + ∫ U, pointFidelity Sf f.value U ∂H.law := by
    unfold transformationAverage
    simp_rw [hpf]
    rw [integral_add (integrable_const _) hint]
    simp
  refine ⟨hdet, hav, ?_⟩
  rw [hav]
  have h0 : 0 ≤ ∫ U, pointFidelity Sf f.value U ∂H.law :=
    integral_nonneg fun U => p06s_pf_nonneg Sf hf f.value U
  linarith
