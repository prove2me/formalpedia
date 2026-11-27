-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_galTorsion___apply_30c217867fca
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:32.449224+00:00
-- url     : https://prove2.me/submissions/b53f06b5-f889-4b7b-add6-b75a27f69574

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
theorem _root_.solution (n : ℕ) (σ : Gal(L/K)) (P : torsionBy (W.baseChange L).toAffine.Point n) :
    (galTorsion.{w} K L W n).ρ σ P = galTorsionHom K L W n σ P := by
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
    | (intros; simp [galTorsionHom, galTorsion]; done)
    | (intros; grind)
    | (intros; grind [galTorsionHom, galTorsion])
    | (intros; unfold galTorsionHom galTorsion; grind)
    | (intros; simp only [galTorsionHom, galTorsion] at * <;> grind)
    | (intros; simp_all [galTorsionHom, galTorsion] <;> grind)
    | (intros; ext <;> grind [galTorsionHom, galTorsion])
    | (intros; constructor <;> intro _ <;> grind [galTorsionHom, galTorsion])
    | (intro x; cases x <;> grind [galTorsionHom, galTorsion])
    | (intro x; induction x <;> simp_all [galTorsionHom, galTorsion])
    | (intro x y; induction x <;> grind [galTorsionHom, galTorsion])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [galTorsionHom, galTorsion])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [galTorsionHom, galTorsion])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_17_1"



