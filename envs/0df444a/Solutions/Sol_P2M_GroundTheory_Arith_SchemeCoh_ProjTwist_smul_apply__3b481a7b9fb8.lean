-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_ProjTwist_smul_apply__3b481a7b9fb8
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:06:19.027868+00:00
-- url     : https://prove2.me/submissions/5186d442-1a79-41ab-9c76-c5e3892e62fb

import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
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
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {𝒜}
open ProjectiveSpectrum
theorem _root_.solution {U : Opens (ProjectiveSpectrum.top 𝒜)} (t : (Proj.structureSheaf 𝒜).obj.obj (op U))
    (f : ∀ x : U, Loc 𝒜 x.1) (x : U) : (t • f) x = (t.1 x).val * f x := by
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
    | (intros; simp [Loc, val]; done)
    | (intros; grind)
    | (intros; grind [Loc, val])
    | (intros; unfold Loc val; grind)
    | (intros; simp only [Loc, val] at * <;> grind)
    | (intros; simp_all [Loc, val] <;> grind)
    | (intros; ext <;> grind [Loc, val])
    | (intros; constructor <;> intro _ <;> grind [Loc, val])
    | (intro x; cases x <;> grind [Loc, val])
    | (intro x; induction x <;> simp_all [Loc, val])
    | (intro x y; induction x <;> grind [Loc, val])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [Loc, val])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [Loc, val])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_52_0"



