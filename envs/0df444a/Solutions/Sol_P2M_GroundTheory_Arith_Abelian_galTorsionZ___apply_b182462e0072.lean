-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_galTorsionZ___apply_b182462e0072
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:31.638193+00:00
-- url     : https://prove2.me/submissions/3389a895-cfec-46c6-bc90-32635ca22514

import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Mathlib
import Mathlib.Tactic





-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open GroundTheory.ProfCoh IntermediateField AddSubgroup WeierstrassCurve
universe w u
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
theorem _root_.solution (n : ℕ) (σ : Gal(L/K))
    (P : torsionBy (W.baseChange L).toAffine.Point n) :
    (galTorsionZ K L W n).ρ σ P = galTorsionHom K L W n σ P := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp [galTorsionHom, galTorsionZ]; done)
    | (intros; grind)
    | (intros; grind [galTorsionHom, galTorsionZ])
    | (intros; unfold galTorsionHom galTorsionZ; grind)
    | (intros; simp only [galTorsionHom, galTorsionZ] at * <;> grind)
    | (intros; simp_all [galTorsionHom, galTorsionZ] <;> grind)
    | (intros; ext <;> grind [galTorsionHom, galTorsionZ])
    | (intros; constructor <;> intro _ <;> grind [galTorsionHom, galTorsionZ])
    | (intro x; cases x <;> grind [galTorsionHom, galTorsionZ])
    | (intro x; induction x <;> simp_all [galTorsionHom, galTorsionZ])
    | (intro x y; induction x <;> grind [galTorsionHom, galTorsionZ])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [galTorsionHom, galTorsionZ])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [galTorsionHom, galTorsionZ])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_17_0"



