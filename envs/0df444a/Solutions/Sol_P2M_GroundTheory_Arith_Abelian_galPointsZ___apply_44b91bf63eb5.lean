-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_galPointsZ___apply_44b91bf63eb5
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:33.132361+00:00
-- url     : https://prove2.me/submissions/10dbb320-cd49-46a2-a17d-dfd88ace5fb8

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
theorem _root_.solution (σ : Gal(L/K)) (P : (W.baseChange L).toAffine.Point) :
    (galPointsZ K L W).ρ σ P = galPointsHom K L W σ P := by
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
    | (intros; simp [galPointsHom, galPointsZ]; done)
    | (intros; grind)
    | (intros; grind [galPointsHom, galPointsZ])
    | (intros; unfold galPointsHom galPointsZ; grind)
    | (intros; simp only [galPointsHom, galPointsZ] at * <;> grind)
    | (intros; simp_all [galPointsHom, galPointsZ] <;> grind)
    | (intros; ext <;> grind [galPointsHom, galPointsZ])
    | (intros; constructor <;> intro _ <;> grind [galPointsHom, galPointsZ])
    | (intro x; cases x <;> grind [galPointsHom, galPointsZ])
    | (intro x; induction x <;> simp_all [galPointsHom, galPointsZ])
    | (intro x y; induction x <;> grind [galPointsHom, galPointsZ])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [galPointsHom, galPointsZ])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [galPointsHom, galPointsZ])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_17_2"



