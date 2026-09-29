-- Prove2me | solution 1 for Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a7d27e4c-02c4-5f5e-9e9f-571ff25e52f1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous

set_option autoImplicit false

universe u v

open MeasureTheory

theorem solution
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    {E : Type v} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (π : Representation ℂ H E) (hπ : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v))
    (P : Submodule ℂ E) (hP : ∀ k : H, ∀ v ∈ P, π k v ∈ P) :
    ∃ Pc : Submodule ℂ E, IsCompl P Pc ∧ ∀ k : H, ∀ v ∈ Pc, π k v ∈ Pc := by
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  classical
  let μ : Measure H := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure μ :=
    ⟨by rw [← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

  obtain ⟨P₀, hP₀⟩ := Submodule.exists_isCompl P
  let p₀ : E →ₗ[ℂ] E := P.subtype ∘ₗ Submodule.linearProjOfIsCompl P P₀ hP₀
  have hp₀P : ∀ v, p₀ v ∈ P := fun v => Submodule.coe_mem _
  have hp₀id : ∀ v ∈ P, p₀ v = v := fun v hv => by
    simp only [p₀, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hP₀ ⟨v, hv⟩)
  let b := Module.finBasis ℂ E

  let X : E → H → E := fun v k => π k (p₀ (π k⁻¹ v))
  have hXcont : ∀ (v : E) (i : Fin (Module.finrank ℂ E)), Continuous fun k => b.coord i (X v k) := by
    intro v i
    have hexp : ∀ k, b.coord i (X v k) =
        ∑ j, b.coord j (π k⁻¹ v) * b.coord i (π k (p₀ (b j))) := by
      intro k
      simp only [X]
      conv_lhs => rw [← b.sum_repr (π k⁻¹ v)]
      simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
    simp_rw [hexp]
    refine continuous_finsetSum _ fun j _ => ?_
    exact ((hπ (b.coord j) v).comp continuous_inv).mul (hπ (b.coord i) (p₀ (b j)))
  let c : E → Fin (Module.finrank ℂ E) → ℂ := fun v i => ∫ k, b.coord i (X v k) ∂μ
  have hci : ∀ (v : E) (i : Fin (Module.finrank ℂ E)), Integrable (fun k => b.coord i (X v k)) μ :=
    fun v i => (hXcont v i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcadd : ∀ v w i, c (v + w) i = c v i + c w i := fun v w i => by
    simp only [c, X, map_add]
    exact integral_add (hci v i) (hci w i)
  have hcsmul : ∀ (a : ℂ) v i, c (a • v) i = a * c v i := fun a v i => by
    simp only [c, X, map_smul, smul_eq_mul]
    exact integral_const_mul a _
  let p : E →ₗ[ℂ] E :=
    { toFun := fun v => ∑ i, c v i • b i
      map_add' := fun v w => by
        simp only [hcadd, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        simp only [hcsmul, RingHom.id_apply, Finset.smul_sum, smul_smul] }

  have hpℓ : ∀ (ℓ : Module.Dual ℂ E) (v : E), ℓ (p v) = ∫ k, ℓ (X v k) ∂μ := by
    intro ℓ v
    have hℓexp : ∀ w : E, ℓ w = ∑ i, b.coord i w * ℓ (b i) := fun w => by
      conv_lhs => rw [← b.sum_repr w]
      simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
    show ℓ (∑ i, c v i • b i) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    simp_rw [hℓexp (X v _)]
    rw [integral_finsetSum _ fun i _ => (hci v i).mul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const]
  have hext : ∀ v w : E, (∀ ℓ : Module.Dual ℂ E, ℓ v = ℓ w) → v = w := fun v w h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ (v - w)]
    intro ℓ; rw [map_sub, h ℓ, sub_self]

  have hpP : ∀ v, p v ∈ P := by
    intro v
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := P), Submodule.mem_dualCoannihilator]
    intro ℓ hℓ
    rw [Submodule.mem_dualAnnihilator] at hℓ
    rw [hpℓ]
    simp [X, hℓ _ (hP _ _ (hp₀P _))]

  have hpid : ∀ v ∈ P, p v = v := by
    intro v hv
    apply hext
    intro ℓ
    rw [hpℓ]
    have : ∀ k, X v k = v := fun k => by
      simp only [X]
      rw [hp₀id _ (hP _ _ hv), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    simp [this]

  have hpeq : ∀ (h : H) (v : E), p (π h v) = π h (p v) := by
    intro h v
    apply hext
    intro ℓ
    rw [hpℓ, show ℓ (π h (p v)) = (ℓ ∘ₗ π h) (p v) from rfl, hpℓ]
    rw [← integral_mul_left_eq_self (fun k => ℓ (X (π h v) k)) h]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only [X, LinearMap.comp_apply]
    rw [mul_inv_rev, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (π h⁻¹) (π h), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

  let p' : E →ₗ[ℂ] P := LinearMap.codRestrict P p hpP
  have hp' : ∀ x : P, p' x = x := fun x => Subtype.ext (hpid x x.2)
  refine ⟨LinearMap.ker p', LinearMap.isCompl_of_proj hp', fun k v hv => ?_⟩
  rw [LinearMap.mem_ker] at hv ⊢
  apply Subtype.ext
  have hv' : p v = 0 := congrArg Subtype.val hv
  show p (π k v) = 0
  rw [hpeq, hv', map_zero]

end S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous
end P2MW
export P2MW.S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous (solution)
