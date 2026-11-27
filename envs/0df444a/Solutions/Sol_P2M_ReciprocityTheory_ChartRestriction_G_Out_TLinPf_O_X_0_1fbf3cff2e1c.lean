-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_O_X_0_1fbf3cff2e1c
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:24:11.573688+00:00
-- url     : https://prove2.me/submissions/a12de04a-d451-428d-b409-36b8d220141e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Mathlib.Tactic




-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
omit [Module O D.toPre.X]
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (P x : T ⟶ D.toPre.P.A) :
    OφX (D := D) P x 0 = (padd D.toPre.P.A P x).left := by
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
    | (intros; simp [R, OφX]; done)
    | (intros; grind)
    | (intros; grind [R, OφX])
    | (intros; unfold R OφX; grind)
    | (intros; simp only [R, OφX] at * <;> grind)
    | (intros; simp_all [R, OφX] <;> grind)
    | (intros; ext <;> grind [R, OφX])
    | (intros; constructor <;> intro _ <;> grind [R, OφX])
    | (intro x; cases x <;> grind [R, OφX])
    | (intro x; induction x <;> simp_all [R, OφX])
    | (intro x y; induction x <;> grind [R, OφX])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [R, OφX])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [R, OφX])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_24_1"



end 
