-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.gauge_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:38.258035+00:00
-- url     : https://prove2.me/submissions/36a79744-7640-4ef7-bd02-05600e7186fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_eval_two_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_bilinearOp_eval_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_bi_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_ac_gen
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_dir_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_dir_same
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_inner_of_derivation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pderiv_eval_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_zero_of_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d n l : ℕ}
variable [Algebra ℚ k]
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O]
    (A : O → Q k d 1) (hA : ∀ a (n) (u v : Q k d n), ac (A a) (u + v) = ac (A a) u + ac (A a) v)
    (aadd : ∀ a b {n} (u : Q k d n), ac (A (a + b)) u = ac (A a) u + ac (A b) u)
    (amul : ∀ a b {n} (u : Q k d n), ac (A (a * b)) u = ac (A a) (ac (A b) u)) (aone : ∀ {n} (u : Q k d n), ac (A 1) u = u)
    (p q : PS k 3 d) (s : PS k 2 d) (ad : O → PS k 2 d)
    (p0 : ∀ {n} (y w : Q k d n), E3 p 0 y w = 0) (p2 : ∀ {n} (x y : Q k d n), E3 p x y 0 = 0)
    (q1 : ∀ {n} (x w : Q k d n), E3 q x 0 w = 0)
    (ps : ∀ {n} (x y w : Q k d n), E3 p x y w = E3 p y x w) (qs : ∀ {n} (x y w : Q k d n), E3 q x y w = E3 q x w y)
    (pc : ∀ {n} (x y t w : Q k d n), E3 p x y w + E3 p (x + y) t w = E3 p y t w + E3 p x (y + t) w)
    (qc : ∀ {n} (x y t w : Q k d n), E3 q x y t + E3 q x (y + t) w = E3 q x t w + E3 q x y (t + w))
    (int : ∀ {n} (x y v w : Q k d n), E3 p x y v + E3 p x y w + E3 q (x + y) v w = E3 q x v w + E3 q y v w + E3 p x y (v + w))
    (si : ∀ {n} (x v : Q k d n), E2 s x v + E2 s v x = 0)
    (sl : ∀ {n} (x v w : Q k d n), E3 q x v w + E2 s x v + E2 s x w = E2 s x (v + w) + E3 p v w x)
    (a1 : ∀ a {n} (x y v : Q k d n), E3 p (ac (A a) x) (ac (A a) y) v + E2 (ad a) (x + y) v =
      E2 (ad a) x v + E2 (ad a) y v + E3 p x y (ac (A (star a)) v))
    (a2 : ∀ a {n} (x v w : Q k d n), E3 q (ac (A a) x) v w + E2 (ad a) x (v + w) =
      E2 (ad a) x v + E2 (ad a) x w + E3 q x (ac (A (star a)) v) (ac (A (star a)) w))
    (am : ∀ a b {n} (x v : Q k d n), E2 (ad (a * b)) x v = E2 (ad a) (ac (A b) x) v + E2 (ad b) x (ac (A (star a)) v))
    (aa : ∀ a b {n} (x v : Q k d n), E3 p (ac (A a) x) (ac (A b) x) v + E2 (ad (a + b)) x v =
      E2 (ad a) x v + E2 (ad b) x v + E3 q x (ac (A (star a)) v) (ac (A (star b)) v))
    (as : ∀ a {n} (x v : Q k d n), E2 (ad a) x v + E2 (ad (star a)) v x + E2 s (ac (A a) x) v = E2 s x (ac (A (star a)) v)) :
    ∃ H : PS k 2 d, (∀ {n} (w : Q k d n), E2 H 0 w = 0) ∧ (∀ {n} (x : Q k d n), E2 H x 0 = 0) ∧
      (∀ {n} (x y w : Q k d n), E3 p x y w = E2 H x w + E2 H y w - E2 H (x + y) w) ∧
      (∀ {n} (x v w : Q k d n), E3 q x v w = E2 H x v + E2 H x w - E2 H x (v + w)) ∧
      (∀ {n} (x v : Q k d n), E2 s x v = E2 H v x - E2 H x v) ∧
      ∀ a {n} (x v : Q k d n), E2 (ad a) x v = E2 H (ac (A a) x) v - E2 H x (ac (A (star a)) v) := by
  obtain ⟨H₀, h₀, z₀, -⟩ := split p p0 ps pc
  let H₁ : PS k 2 d := H₀ - E2 H₀ (gen 0) 0
  have e₁ : ∀ {n} (x w : Q k d n), E2 H₁ x w = E2 H₀ x w - E2 H₀ x 0 := fun x w => by simp [H₁, eval_two_sub, eval_two_eval_two]
  have h₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H₁ x w + E2 H₁ y w - E2 H₁ (x + y) w := fun x y w => by
    have := h₀ x y 0
    rw [p2] at this
    rw [e₁, e₁, e₁, h₀]; linear_combination -this
  have z₁ : ∀ {n} (x : Q k d n), E2 H₁ x 0 = 0 := fun x => by rw [e₁, sub_self]
  let b : PS k 3 d := E3 q (gen 2) (gen 0) (gen 1) -
    (E2 H₁ (gen 2) (gen 0) + E2 H₁ (gen 2) (gen 1) - E2 H₁ (gen 2) (gen 0 + gen 1))
  have eb : ∀ {n} (v w x : Q k d n), E3 b v w x = E3 q x v w - (E2 H₁ x v + E2 H₁ x w - E2 H₁ x (v + w)) := fun v w x => by
    show sb _ _ = _
    simp only [b, map_sub, map_add, formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtTwoPoints, sq_gen]; rfl
  obtain ⟨H₂, h₂, z₂, n₂⟩ := split b (fun y w => by rw [eb, q1, z₁, zero_add, zero_add]; ring)
    (fun x y w => by rw [eb, eb, qs, add_comm x y]; ring)
    (fun x y t w => by rw [eb, eb, eb, eb, add_assoc x]; linear_combination qc w x y t)
  let D : PS k 3 d := E2 H₂ (gen 2) (gen 0) + E2 H₂ (gen 2) (gen 1) - E2 H₂ (gen 2) (gen 0 + gen 1)
  have eD : ∀ {n} (x y v : Q k d n), E3 D x y v = E2 H₂ v x + E2 H₂ v y - E2 H₂ v (x + y) := fun x y v => by
    show sb _ _ = _
    simp only [D, map_sub, map_add, formalPointSubstitutionSeries_valueAtTwoPoints, sq_gen]; rfl
  have D0 : D = 0 := zero_of_add D (fun x y v w => by
      have c₁ := h₂ v w x; have c₂ := h₂ v w y; have c₃ := h₂ v w (x + y)
      rw [eb] at c₁ c₂ c₃
      rw [eD, eD, eD]
      linear_combination c₁ + c₂ - c₃ + int x y v w - h₁ x y v - h₁ x y w + h₁ x y (v + w)) fun c x y => by
    have d₀ := dir_ne (k := k) (d := d) (show (0 : Fin 3) ≠ 2 by decide)
    have d₁ := dir_ne (k := k) (d := d) (show (1 : Fin 3) ≠ 2 by decide)
    rw [map_sub, map_add, pderiv_eval_two (dir_same 2) d₀, pderiv_eval_two (dir_same 2) d₁, pderiv_eval_two (dir_same 2) (d₀.add d₁)]
    simp [E3, n₂]
  have ad₂ : ∀ {n} (x y v : Q k d n), E2 H₂ v (x + y) = E2 H₂ v x + E2 H₂ v y := fun x y v => by
    have := eD x y v
    rw [D0, E3, map_zero] at this
    linear_combination this
  let H₃ : PS k 2 d := H₁ + E2 H₂ (gen 1) (gen 0)
  have e₃ : ∀ {n} (x w : Q k d n), E2 H₃ x w = E2 H₁ x w + E2 H₂ w x := fun x w => by simp [H₃, eval_two_add, eval_two_eval_two]
  have g₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H₃ x w + E2 H₃ y w - E2 H₃ (x + y) w := fun x y w => by
    rw [e₃, e₃, e₃, h₁, ad₂]; ring
  have g₂ : ∀ {n} (x v w : Q k d n), E3 q x v w = E2 H₃ x v + E2 H₃ x w - E2 H₃ x (v + w) := fun x v w => by
    have := h₂ v w x
    rw [eb] at this
    rw [e₃, e₃, e₃]; linear_combination this
  let s' : PS k 2 d := s - (E2 H₃ (gen 1) (gen 0) - H₃)
  have es : ∀ {n} (x v : Q k d n), E2 s' x v = E2 s x v - (E2 H₃ v x - E2 H₃ x v) := fun x v => by simp [s', eval_two_sub, eval_two_eval_two]
  have s₂ : ∀ {n} (x v w : Q k d n), E2 s' x (v + w) = E2 s' x v + E2 s' x w := fun x v w => by
    rw [es, es, es]; linear_combination g₂ x v w - g₁ v w x - sl x v w
  have sa : ∀ {n} (x v : Q k d n), E2 s' x v = -E2 s' v x := fun x v => by rw [es, es]; linear_combination si x v
  have s₁ : ∀ {n} (x y v : Q k d n), E2 s' (x + y) v = E2 s' x v + E2 s' y v := fun x y v => by
    rw [sa, s₂, sa x, sa y]; ring
  let H₄ : PS k 2 d := H₃ - (1 / 2 : ℚ) • s'
  have e₄ : ∀ {n} (x w : Q k d n), E2 H₄ x w = E2 H₃ x w - (1 / 2 : ℚ) • E2 s' x w := fun x w => by
    rw [eval_two_sub, eval_two_smul]
  have f₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H₄ x w + E2 H₄ y w - E2 H₄ (x + y) w := fun x y w => by
    rw [e₄, e₄, e₄, g₁, s₁]; module
  have f₂ : ∀ {n} (x v w : Q k d n), E3 q x v w = E2 H₄ x v + E2 H₄ x w - E2 H₄ x (v + w) := fun x v w => by
    rw [e₄, e₄, e₄, g₂, s₂]; module
  have f₃ : ∀ {n} (x v : Q k d n), E2 s x v = E2 H₄ v x - E2 H₄ x v := fun x v => by
    rw [e₄, e₄, sa v x, eq_add_of_sub_eq (es x v).symm]; module
  let dd : O → PS k 2 d := fun a => ad a - (E2 H₄ (ac (A a) (gen 0)) (gen 1) - E2 H₄ (gen 0) (ac (A (star a)) (gen 1)))
  have ed : ∀ a {n} (x v : Q k d n), E2 (dd a) x v = E2 (ad a) x v - (E2 H₄ (ac (A a) x) v - E2 H₄ x (ac (A (star a)) v)) :=
    fun a n x v => by simp [dd, eval_two_sub, eval_two_eval_two]
  have hdd : ∀ a, dd a ∈ Bi k d := fun a => ⟨fun n x y v => by
      rw [ed, ed, ed, hA]; linear_combination a1 a x y v - f₁ (ac (A a) x) (ac (A a) y) v + f₁ x y (ac (A (star a)) v),
    fun n x v w => by
      rw [ed, ed, ed, hA]
      linear_combination a2 a x v w - f₂ (ac (A a) x) v w + f₂ x (ac (A (star a)) v) (ac (A (star a)) w)⟩
  have h1 : ∀ (n) (u v : Q k d n), ac (gen 0) (u + v) = ac (gen 0) u + ac (gen 0) v := fun n u v => by simp only [ac_gen]
  have ext := @bi_ext k _ d _
  let Lh : O →+* Module.End ℚ (Bi k d) := RingHom.mk' ⟨⟨fun a => biOp (gen 0) (A (star a)) h1 (hA _),
      LinearMap.ext fun f => ext (by rw [bilinearOp_eval_two, ac_gen, star_one, aone]; rfl)⟩,
      fun a b => LinearMap.ext fun f => ext (by
        rw [Module.End.mul_apply, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, ac_gen, ac_gen, star_mul, amul])⟩
    fun a b => LinearMap.ext fun f => ext (by
      show E2 (biOp _ _ h1 (hA _) f).1 _ _ = E2 ((biOp _ _ h1 (hA _) f).1 + (biOp _ _ h1 (hA _) f).1) _ _
      rw [eval_two_add, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, star_add, aadd, f.2.2])
  let Rh : O →+* Module.End ℚ (Bi k d) := RingHom.mk' ⟨⟨fun a => biOp (A a) (gen 0) (hA _) h1,
      LinearMap.ext fun f => ext (by rw [bilinearOp_eval_two, ac_gen, aone]; rfl)⟩,
      fun a b => LinearMap.ext fun f => ext (by
        rw [Module.End.mul_apply, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, ac_gen, ac_gen, mul_comm, amul])⟩
    fun a b => LinearMap.ext fun f => ext (by
      show E2 (biOp _ _ (hA _) h1 f).1 _ _ = E2 ((biOp _ _ (hA _) h1 f).1 + (biOp _ _ (hA _) h1 f).1) _ _
      rw [eval_two_add, bilinearOp_eval_two, bilinearOp_eval_two, bilinearOp_eval_two, aadd, f.2.1])
  have eL : ∀ a (f : Bi k d) {n} (x v : Q k d n), E2 (Lh a f).1 x v = E2 f.1 x (ac (A (star a)) v) := fun a f n x v =>
    (bilinearOp_eval_two _ _ h1 (hA _) f x v).trans (by rw [ac_gen])
  have eR : ∀ a (f : Bi k d) {n} (x v : Q k d n), E2 (Rh a f).1 x v = E2 f.1 (ac (A a) x) v := fun a f n x v =>
    (bilinearOp_eval_two _ _ (hA _) h1 f x v).trans (by rw [ac_gen])
  obtain ⟨β, hβ⟩ := inner_of_derivation Lh Rh (fun a b => LinearMap.ext fun f => ext (by
      simp only [Module.End.mul_apply, eL, eR])) (AddMonoidHom.mk' (fun a => ⟨dd a, hdd a⟩) fun a b => ext (by
      show E2 (dd (a + b)) _ _ = E2 (dd a + dd b) _ _
      rw [eval_two_add, ed, ed, ed, star_add, aadd, aadd]
      linear_combination aa a b (gen 0 : Q k d 2) (gen 1) - f₁ (ac (A a) (gen 0 : Q k d 2)) (ac (A b) (gen 0)) (gen 1) +
        f₂ (gen 0 : Q k d 2) (ac (A (star a)) (gen 1)) (ac (A (star b)) (gen 1)))) fun a b => ext (by
      show E2 (dd (a * b)) _ _ = E2 ((Rh b ⟨dd a, hdd a⟩).1 + (Lh a ⟨dd b, hdd b⟩).1) _ _
      rw [eval_two_add, eR, eL, ed, ed, ed, am, star_mul, amul, amul]; ring)
  have hβ' : ∀ a {n} (x v : Q k d n), E2 (dd a) x v = E2 β.1 (ac (A a) x) v - E2 β.1 x (ac (A (star a)) v) :=
    fun a n x v => by rw [← eR, ← eL, ← eval_two_sub]; exact congrArg (fun f : Bi k d => E2 f.1 x v) (hβ a)
  let H : PS k 2 d := H₄ + (1 / 2 : ℚ) • (β.1 + E2 β.1 (gen 1) (gen 0))
  have e : ∀ {n} (x w : Q k d n), E2 H x w = E2 H₄ x w + (1 / 2 : ℚ) • (E2 β.1 x w + E2 β.1 w x) := fun x w => by
    simp only [H, eval_two_add, eval_two_smul, eval_two_eval_two, sq_gen]; rfl
  have r₁ : ∀ {n} (x y w : Q k d n), E3 p x y w = E2 H x w + E2 H y w - E2 H (x + y) w := fun x y w => by
    rw [e, e, e, f₁, β.2.1, β.2.2]; module
  have r₂ : ∀ {n} (x v w : Q k d n), E3 q x v w = E2 H x v + E2 H x w - E2 H x (v + w) := fun x v w => by
    rw [e, e, e, f₂, β.2.1, β.2.2]; module
  refine ⟨H, fun w => ?_, fun x => ?_, r₁, r₂, fun x v => by rw [e, e, f₃]; module, fun a n x v => ?_⟩
  · have := r₁ 0 0 w
    rw [p0, add_zero] at this; linear_combination -this
  · have := r₂ x 0 0
    rw [q1, add_zero] at this; linear_combination -this
  · have c₁ := hβ' a x v
    have c₂ := hβ' (star a) v x
    have c₃ := as a x v
    rw [ed] at c₁ c₂
    rw [star_star] at c₂
    rw [f₃, f₃] at c₃
    rw [e, e]
    linear_combination (norm := module) (1 / 2 : ℚ) • c₁ - (1 / 2 : ℚ) • c₂ + (1 / 2 : ℚ) • c₃
end ReciprocityTheory.ChartRestriction.G.TB.Canon
