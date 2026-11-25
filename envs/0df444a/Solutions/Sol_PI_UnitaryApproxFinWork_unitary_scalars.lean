-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.unitary_scalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:20.153892+00:00
-- url     : https://prove2.me/submissions/4d7b72d1-acb2-426f-94b0-41b12fdf3c91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_UnitaryScalars
import Theorems.Thm_PI_UnitaryApproxFinWork_wa_valued_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution : UnitS := by
  intro F E _ _ _ _ _ v π hπ s hs
  classical
  let O := v.adicCompletionIntegers F
  let S := Sv E v
  have hgen2 : ∀ y : O, ((1 : E) ⊗ₜ[F] (y : v.adicCompletion F)) ∈ S := by
    intro y
    exact Subring.subset_closure (Or.inr ⟨⟨y, y.2⟩, rfl⟩)
  let ψ : O →+* E ⊗[F] v.adicCompletion F :=
    (Algebra.TensorProduct.includeRight :
      v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F).toRingHom.comp O.subtype
  have hψ : ∀ y : O, ψ y = (1 : E) ⊗ₜ[F] (y : v.adicCompletion F) := fun y => rfl
  let φ : O →+* S := ψ.codRestrict S (fun y => by rw [hψ]; exact hgen2 y)
  letI : Algebra O (E ⊗[F] v.adicCompletion F) := ψ.toAlgebra
  letI : Algebra O S := φ.toAlgebra
  let f : S →ₐ[O] E ⊗[F] v.adicCompletion F := { S.subtype with commutes' := fun r => rfl }
  have hle : S ≤ (integralClosure O (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hx
      obtain ⟨p, hpm, hp⟩ := NumberField.RingOfIntegers.isIntegral_coe z
      refine ⟨p.map (Int.castRingHom O), hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap O (E ⊗[F] v.adicCompletion F)).comp (Int.castRingHom O) =
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E)).comp (algebraMap ℤ E) :=
        RingHom.ext_int _ _
      rw [hcomp]
      have := Polynomial.hom_eval₂ p (algebraMap ℤ E) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E))
        (algebraMap (𝓞 E) E z)
      rw [hp, map_zero] at this
      exact this.symm
    · exact isIntegral_algebraMap (x := (⟨y, hy⟩ : O))
  have hIntS : Algebra.IsIntegral O S :=
    ⟨fun x => (isIntegral_algHom_iff f Subtype.val_injective).1 (hle x.2)⟩
  have hπv : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    rw [wa_valued_algebraMap]
    exact (valuation_lt_one_iff_mem v π).2 hπ
  let πO : O := ⟨algebraMap F (v.adicCompletion F) (π : F), by
    rw [mem_adicCompletionIntegers]; exact hπv.le⟩
  have hπmax : πO ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have h1 : Valued.v (w : v.adicCompletion F) ≤ 1 := by
      have := w.2
      rwa [mem_adicCompletionIntegers] at this
    have h2 : algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F) = 1 :=
      congrArg Subtype.val hw
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F)) < 1 :=
      calc _ = Valued.v (algebraMap F (v.adicCompletion F) (π : F)) *
            Valued.v (w : v.adicCompletion F) := map_mul _ _ _
        _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (π : F)) * 1 := mul_le_mul' le_rfl h1
        _ < 1 := by rw [mul_one]; exact hπv
    rw [h2, map_one] at h3
    exact lt_irrefl _ h3
  have hd : dv E v π = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F) := by
    simp only [dv, PI.UnitaryApproxDefs.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul _ _ _
  have hxS : 1 + dv E v π * s ∈ S :=
    S.add_mem S.one_mem (S.mul_mem (by rw [hd]; exact hgen2 πO) hs)
  have key : IsUnit (⟨1 + dv E v π * s, hxS⟩ : S) := by
    by_contra h
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
    have hP : (M.comap (algebraMap O S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have hπM : algebraMap O S πO ∈ M := by
      have : πO ∈ M.comap (algebraMap O S) := by
        rw [IsLocalRing.eq_maximalIdeal hP]; exact hπmax
      exact this
    have e : (1 : S) = ⟨1 + dv E v π * s, hxS⟩ - algebraMap O S πO * ⟨s, hs⟩ := by
      apply Subtype.ext
      change (1 : E ⊗[F] v.adicCompletion F) = (1 + dv E v π * s) -
        ((1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F)) * s
      rw [hd]; ring
    have h1 : (1 : S) ∈ M := by
      rw [e]; exact M.sub_mem hxM (M.mul_mem_right _ hπM)
    exact hM.ne_top ((Ideal.eq_top_iff_one M).2 h1)
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 key
  exact ⟨w, w.2, congrArg Subtype.val hw⟩
end PI.UnitaryApproxFinWork
