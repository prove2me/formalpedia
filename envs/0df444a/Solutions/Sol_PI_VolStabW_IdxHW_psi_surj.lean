-- Prove2me | solution 1 for PI.VolStabW.IdxHW.psi_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:16.004814+00:00
-- url     : https://prove2.me/submissions/e18576fb-760d-45e8-ab17-3930669f98a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxC
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxD
import Theorems.Thm_PI_VolStabW_HasDens_le
import Theorems.Thm_PI_VolStabW_IdxHW_cr_sig
import Theorems.Thm_PI_VolStabW_IdxHW_cr_smul_one
import Theorems.Thm_PI_VolStabW_IdxHW_cr_symm
import Theorems.Thm_PI_VolStabW_IdxHW_crdS_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
namespace PI.VolStabW.IdxHW
theorem _root_.solution (k0 : Fin 2) (hσ : ∀ x, σ (σ x) = x)
    (hC : ∀ k l, algebraMap F (Fv F v) (Cmat b σ k l) ∈ v.adicCompletionIntegers F)
    (hu : ∀ k, algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) ∈ v.adicCompletionIntegers F)
    (hk0 : b.repr 1 k0 ≠ 0) : Function.Surjective (psi b v σ a k0) := by
  classical
  intro z
  let T : Fv F v → Fv F v → Fv F v ⊗[F] E := fun p q =>
    (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm ![p, q]
  have cT : ∀ p q k, cr b v (T p q) k = ![p, q] k := fun p q k => cr_symm b v _ k
  have hu0 : algebraMap F (Fv F v) (b.repr 1 k0) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F (Fv F v)).injective]; exact hk0
  let t : Fin a → Fv F v := fun i => (z (i, i) : Fv F v) * (algebraMap F (Fv F v) (b.repr 1 k0))⁻¹
  let Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then T (z (i, j)) (z (j, i))
    else if j < i then sigR (Fv F v) σ (T (z (j, i)) (z (i, j))) else t i • 1
  have hY : Y ∈ HermR (Fv F v) σ a := by
    intro i j
    show sigR (Fv F v) σ (Y j i) = Y i j
    rcases lt_trichotomy i j with h | h | h
    · simp only [Y, if_pos h, if_neg (not_lt.2 h.le)]
      exact sigR_invol (Fv F v) σ hσ _
    · subst h
      simp only [Y, lt_irrefl, if_false]
      rw [Algebra.smul_def, mul_one, sigR_algebraMap]
    · simp only [Y, if_pos h, if_neg (not_lt.2 h.le)]
  let S : HermR (Fv F v) σ a := ⟨Y, hY⟩
  have hSY : ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = Y i j := fun _ _ => rfl
  have hSO : S ∈ hermO b v σ a := by
    refine (mem_hermO_iff b v σ a S).2 fun i j k => ?_
    rw [crdS_eq, hSY]
    rcases lt_trichotomy i j with h | h | h
    · simp only [Y, if_pos h, cT]
      fin_cases k
      · exact (z (i, j)).2
      · exact (z (j, i)).2
    · subst h
      simp only [Y, lt_irrefl, if_false, cr_smul_one]
      have e : t i * algebraMap F (Fv F v) (b.repr 1 k) =
          (z (i, i) : Fv F v) * algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) := by
        simp only [t, map_div₀]
        field_simp
      rw [e]
      exact mul_mem (z (i, i)).2 (hu k)
    · simp only [Y, if_neg (not_lt.2 h.le), if_pos h, cr_sig, Fin.sum_univ_two, cT]
      refine add_mem (mul_mem (hC _ _) ?_) (mul_mem (hC _ _) ?_)
      · exact (z (j, i)).2
      · exact (z (i, j)).2
  refine ⟨⟨S, hSO⟩, ?_⟩
  funext q
  obtain ⟨i, j⟩ := q
  apply Subtype.ext
  rcases lt_trichotomy i j with h | h | h
  · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos h, crdS_eq, hSY]
    simp only [Y, if_pos h, cT]
    rfl
  · subst h
    simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false, crdS_eq, hSY]
    simp only [Y, lt_irrefl, if_false, cr_smul_one, t]
    rw [inv_mul_cancel_right₀ hu0]
  · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 h.le), if_pos h,
      crdS_eq, hSY]
    simp only [Y, if_pos h, cT]
    rfl
end PI.VolStabW.IdxHW
