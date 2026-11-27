-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:38:40.166426+00:00
-- url     : https://prove2.me/submissions/bc05b26c-121c-4e76-aad1-4ea4804155f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ptJ_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ptJ_aug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ptJ_trunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ptJ_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_ptJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ptJ_zero
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_ac_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_op_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
variable {x} (hx : IsUnivChart G d x)
include hx
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [IsCommMonObj G] {O : Type} [CommRing O] (a : Geo.Tor.OAct O G) :
    ∃ (F : FGLaw R d) (A : OAct O F),
      (∀ m, ptJ x m (⟨F.F, F.const⟩ : Q R d 2) = ptJ x m (gen 0) * ptJ x m (gen 1)) ∧
      ∀ c m, ptJ x m (⟨A.act c, A.const c⟩ : Q R d 1) = ptJ x m (gen 0) ≫ a.act c := by
  obtain ⟨F, hF⟩ := exists_ptJ hx (fun m => ptJ x m (gen 0 : Q R d 2) * ptJ x m (gen 1))
    (fun m => by rw [MonObj.comp_mul, ptJ_aug hx, ptJ_aug hx, _root_.mul_one])
    (fun m => by rw [MonObj.comp_mul, ptJ_trunc hx, ptJ_trunc hx])
  choose A hA using fun c => exists_ptJ hx (fun m => ptJ x m (gen 0 : Q R d 1) ≫ a.act c)
    (fun m => by have := a.hom c; rw [← Category.assoc, ptJ_aug hx, MonObj.one_comp])
    (fun m => by rw [← Category.assoc, ptJ_trunc hx])
  have vF : ∀ {n} m (u v : Q R d n), ptJ x m (op F u v) = ptJ x m u * ptJ x m v := fun m u v => by
    rw [op, ← ptJ_sq, hF, MonObj.comp_mul, ptJ_sq, ptJ_sq, sq_gen, sq_gen]; rfl
  have vA : ∀ c {n} m (u : Q R d n), ptJ x m (ac (A c) u) = ptJ x m u ≫ a.act c := fun c n m u => by
    rw [ac, ← ptJ_sq, hA, ← Category.assoc, ptJ_sq, sq_gen]; rfl
  have val := fun {n} {p q : Q R d n} (h : ∀ m, ptJ x m p = ptJ x m q) => congrArg Subtype.val (ptJ_inj hx h)
  refine ⟨⟨F.1, F.2, fun i => ?_, fun i => ?_, fun i => ?_⟩, ⟨fun c => (A c).1, fun c => (A c).2, fun c => ?_, fun c c' => ?_,
    fun c c' => ?_, ?_⟩, hF, hA⟩
  · have := val (p := op F 0 (gen 0 : Q R d 1)) (q := gen 0) fun m => by rw [vF, ptJ_zero hx, _root_.one_mul]
    rw [op_val] at this; exact congrFun this i
  · have := val (p := op F (gen 1) (gen 0 : Q R d 2)) (q := F) fun m => by rw [vF, hF, mul_comm]
    rw [op_val] at this; exact congrFun this i
  · have := val (p := op F (op F (gen 0) (gen 1)) (gen 2 : Q R d 3)) (q := op F (gen 0) (op F (gen 1) (gen 2))) fun m => by
      simp only [vF, _root_.mul_assoc]
    simp only [op_val] at this; exact congrFun this i
  · have := val (p := ac (A c) (op F (gen 0) (gen 1 : Q R d 2))) (q := op F (ac (A c) (gen 0)) (ac (A c) (gen 1))) fun m => by
      have := a.hom c
      simp only [vF, vA, MonObj.mul_comp]
    simp only [op_val, ac_val] at this; exact this
  · have := val (p := A (c + c')) (q := op F (A c) (A c')) fun m => by rw [vF, hA, hA, hA, a.add, MonObj.comp_mul]
    rw [op_val] at this; exact this
  · have := val (p := A (c * c')) (q := ac (A c) (A c')) fun m => by rw [vA, hA, hA, mul_comm, a.mul, Category.assoc]
    rw [ac_val] at this; exact this
  · exact val (p := A 1) (q := gen 0) fun m => by rw [hA, a.one, Category.comp_id]
end ReciprocityTheory.ChartRestriction.G.Chart
