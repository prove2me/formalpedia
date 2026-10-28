-- Prove2me | solution 1 for StrictTwoGroups.TwoEquiv.twoGrp_isStrict2Category
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:51:40.292734+00:00
-- url     : https://prove2.me/submissions/33370817-0007-43a3-bcfe-1d6eb1eaf3d5

import Definitions.Def_StrictTwoGroups_TwoEquiv_CrossedModule
import Definitions.Def_StrictTwoGroups_TwoEquiv_Raw2Cat
import Definitions.Def_StrictTwoGroups_TwoEquiv_StrictTwoGroup
import Definitions.Def_StrictTwoGroups_TwoEquiv_XMod
import Definitions.Def_StrictTwoGroups_TwoEquiv_TwoGrp
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors
import Definitions.Def_StrictTwoGroups_TwoEquiv_RoundTrip
import Init
import Mathlib






section
set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv
universe u

/-- Units and interchange already determine composition on composable pairs. -/
theorem composition_from_units_interchange (G : StrictTwoGroup.{u})
    (hunit : ∀ a, G.comp a (G.i (G.s a)) = a ∧ G.comp (G.i (G.t a)) a = a)
    (hinter : ∀ a b a' b', G.s a = G.t b → G.s a' = G.t b' →
      G.comp (a * a') (b * b') = G.comp a b * G.comp a' b')
    (a b : G.G1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b := by
  let y := (G.i (G.s a))⁻¹ * b
  have hty : G.t y = 1 := by
    simp [y, map_mul, map_inv, G.t_i, hab]
  have hleft : G.comp 1 y = y := by
    simpa [hty] using (hunit y).2
  have h := hinter a (G.i (G.s a)) 1 y (by rw [G.t_i]) (by simp [hty])
  simpa [y, mul_assoc, (hunit a).1, hleft] using h

theorem proposition_comp_formula (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b :=
  composition_from_units_interchange G hG.2.1 hG.2.2.2 a b hab

theorem corollary_comp_ker (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (ha : G.s a = 1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b ∧ G.comp a b = a * b := by
  have h := proposition_comp_formula G hG a b hab
  exact ⟨h, by simpa [ha] using h⟩

end StrictTwoGroups.TwoEquiv

universe u
theorem composition_solution (G : StrictTwoGroups.TwoEquiv.StrictTwoGroup.{u})
    (hG : StrictTwoGroups.TwoEquiv.IsStrictTwoGroup G) (a b : G.G1)
    (hab : G.s a = G.t b) : G.comp a b = a * (G.i (G.s a))⁻¹ * b :=
  StrictTwoGroups.TwoEquiv.proposition_comp_formula G hG a b hab

end


section
set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv
universe u

theorem source_kernel_part (G : StrictTwoGroup.{u}) (a : G.G1) :
    a * (G.i (G.s a))⁻¹ ∈ G.s.ker := by
  simp [MonoidHom.mem_ker, G.s_i]

/-- The source retraction splits the arrow group; category axioms are unnecessary. -/
def sourceSplit (G : StrictTwoGroup.{u}) :
    G.G1 ≃* (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0) where
  toFun a := ⟨⟨a * (G.i (G.s a))⁻¹, source_kernel_part G a⟩, G.s a⟩
  invFun x := (x.left : G.G1) * G.i x.right
  left_inv a := by simp [mul_assoc]
  right_inv x := by
    have hx : G.s (x.left : G.G1) = 1 := x.left.property
    apply SemidirectProduct.ext
    · apply Subtype.ext
      simp only [map_mul, G.s_i, hx, one_mul]
      simp [mul_assoc]
    · simp only [map_mul, G.s_i, hx, one_mul]
  map_mul' a b := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      simp only [SemidirectProduct.mul_left, Subgroup.coe_mul,
        MonoidHom.comp_apply, MulAut.conjNormal_apply, map_mul, mul_inv_rev]
      group
    · exact map_mul G.s a b

theorem sourceSplit_left (G : StrictTwoGroup.{u}) (a : G.G1) :
    ((sourceSplit G a).left : G.G1) = a * (G.i (G.s a))⁻¹ := rfl

theorem sourceSplit_right (G : StrictTwoGroup.{u}) (a : G.G1) :
    (sourceSplit G a).right = G.s a := rfl

theorem sourceSplit_symm (G : StrictTwoGroup.{u})
    (x : ↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0) :
    (sourceSplit G).symm x = (x.left : G.G1) * G.i x.right := rfl

theorem phi_mulEquiv (G : StrictTwoGroup.{u}) :
    ∃ e : G.G1 ≃* (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0),
      (∀ a, ((e a).left : G.G1) = a * (G.i (G.s a))⁻¹ ∧ (e a).right = G.s a) ∧
      ∀ x, e.symm x = (x.left : G.G1) * G.i x.right := by
  exact ⟨sourceSplit G, fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

end StrictTwoGroups.TwoEquiv

end


section
set_option autoImplicit false

namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv
universe u

/-- A strict two-group whose arrow group is noncommutative when `H` is. -/
def pairGroupoid (H : Type u) [Group H] : StrictTwoGroup.{u} where
  G0 := H
  G1 := H × H
  s := MonoidHom.snd H H
  t := MonoidHom.fst H H
  i := (MonoidHom.id H).prod (MonoidHom.id H)
  comp a b := (a.1, b.2)
  s_i _ := rfl
  t_i _ := rfl

theorem pairGroupoid_strict (H : Type u) [Group H] :
    IsStrictTwoGroup (pairGroupoid H) := by
  constructor
  · intro a b _
    exact ⟨rfl, rfl⟩
  constructor
  · intro a
    exact ⟨rfl, rfl⟩
  constructor
  · intro a b c _ _
    rfl
  · intro a b a' b' _ _
    rfl

abbrev p : Equiv.Perm (Fin 3) := Equiv.swap 0 1
abbrev q : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem permutations_do_not_commute : p * q ≠ q * p := by decide

/-- Reversing the factor order in the kernel coordinate changes the result. -/
theorem reversed_kernel_coordinate_fails :
    let G := pairGroupoid (Equiv.Perm (Fin 3))
    let a : G.G1 := (p, q)
    a * (G.i (G.s a))⁻¹ ≠ (G.i (G.s a))⁻¹ * a := by
  change ((p, q) * (q, q)⁻¹ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ≠
    (q, q)⁻¹ * (p, q)
  decide

/-- The formula is only asserted for composable arrows. -/
theorem noncomposable_formula_fails :
    let G := pairGroupoid (Equiv.Perm (Fin 3))
    let a : G.G1 := (1, 1)
    let b : G.G1 := (p, 1)
    G.s a ≠ G.t b ∧ G.comp a b ≠ a * (G.i (G.s a))⁻¹ * b := by
  change (1 : Equiv.Perm (Fin 3)) ≠ p ∧
    ((1, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ≠
      ((1, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) *
      ((1, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))⁻¹ *
      ((p, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  decide

end Queelius.StrictTwoGroups.Controls

end

section
set_option autoImplicit false
namespace StrictTwoGroups.TwoEquiv
universe u

theorem source_target_kernel_commute (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (ha : G.s a = 1) (hb : G.t b = 1) : a * b = b * a := by
  have h1b : G.comp 1 b = b := by simpa [hb] using (hG.2.1 b).2
  have ha1 : G.comp a 1 = a := by simpa [ha] using (hG.2.1 a).1
  have hi := hG.2.2.2 1 b a 1 (by simp [hb]) (by simp [ha])
  calc
    a*b = G.comp a b := ((corollary_comp_ker G hG a b ha (ha.trans hb.symm)).2).symm
    _ = b*a := by simpa [h1b,ha1] using hi

theorem source_kernel_peiffer (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (h h' : ↥G.s.ker) :
    G.i (G.t h) * (h' : G.G1) * (G.i (G.t h))⁻¹ = (h : G.G1) * h' * (h : G.G1)⁻¹ := by
  let z := (G.i (G.t h))⁻¹ * (h : G.G1)
  have hz : G.t z = 1 := by simp [z, G.t_i]
  have hc := source_target_kernel_commute G hG (h' : G.G1) z h'.property hz
  calc
    _ = G.i (G.t h) * ((h' : G.G1)*z) * (h : G.G1)⁻¹ := by dsimp [z]; group
    _ = G.i (G.t h) * (z*(h' : G.G1)) * (h : G.G1)⁻¹ := by rw [hc]
    _ = _ := by dsimp [z]; group

theorem toXMod_isCrossedModule (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G) :
    IsCrossedModule (toXMod G) := by
  intro h h'
  apply Subtype.ext
  exact source_kernel_peiffer G hG h h'

end StrictTwoGroups.TwoEquiv
universe u
theorem object_solution (G : StrictTwoGroups.TwoEquiv.StrictTwoGroup.{u})
    (hG : StrictTwoGroups.TwoEquiv.IsStrictTwoGroup G) :
    StrictTwoGroups.TwoEquiv.IsCrossedModule (StrictTwoGroups.TwoEquiv.toXMod G) :=
  StrictTwoGroups.TwoEquiv.toXMod_isCrossedModule G hG

end

section
set_option autoImplicit false
namespace StrictTwoGroups.TwoEquiv
universe u

theorem toTwoGrp_isStrictTwoGroup (χ : CrossedModule.{u}) (hχ : IsCrossedModule χ) :
    IsStrictTwoGroup (toTwoGrp χ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b hab
    change a.right = χ.τ b.left * b.right at hab
    constructor
    · rfl
    · change χ.τ (a.left*b.left)*b.right = χ.τ a.left*a.right
      rw [map_mul,hab,mul_assoc]
  · intro a
    constructor
    · apply SemidirectProduct.ext
      · change a.left*1=a.left
        exact mul_one _
      · rfl
    · apply SemidirectProduct.ext
      · change 1*a.left=a.left
        exact one_mul _
      · rfl
  · intro a b c hab hbc
    apply SemidirectProduct.ext
    · exact mul_assoc _ _ _
    · rfl
  · intro a b a' b' hab hab'
    change a.right = χ.τ b.left * b.right at hab
    apply SemidirectProduct.ext
    · change (a.left * χ.α a.right a'.left) * (b.left * χ.α b.right b'.left) =
        (a.left*b.left)*χ.α b.right (a'.left*b'.left)
      rw [hab, map_mul, MulAut.mul_apply, hχ, map_mul]
      group
    · rfl

end StrictTwoGroups.TwoEquiv

end

section
set_option autoImplicit false
namespace StrictTwoGroups.TwoEquiv
universe u

theorem peiffer_of_toTwoGrp_strict (χ : CrossedModule.{u})
    (hG : IsStrictTwoGroup (toTwoGrp χ)) : IsCrossedModule χ := by
  intro h h'
  let a : χ.H ⋊[χ.α] χ.G := ⟨1,χ.τ h⟩
  let b : χ.H ⋊[χ.α] χ.G := ⟨h,1⟩
  let a' : χ.H ⋊[χ.α] χ.G := ⟨h',1⟩
  have hi := hG.2.2.2 a b a' 1
    (by change χ.τ h = χ.τ h*1; simp)
    (by change (1:χ.G) = χ.τ 1*1; simp)
  have hl := congrArg SemidirectProduct.left hi
  change (1*χ.α (χ.τ h) h')*(h*χ.α 1 1) = (1*h)*χ.α 1 (h'*1) at hl
  have he : χ.α (χ.τ h) h' * h = h*h' := by
    simpa using hl
  exact (eq_mul_inv_iff_mul_eq).mpr he

theorem toTwoGrp_strict_iff (χ : CrossedModule.{u}) :
    IsStrictTwoGroup (toTwoGrp χ) ↔ IsCrossedModule χ :=
  ⟨peiffer_of_toTwoGrp_strict χ,toTwoGrp_isStrictTwoGroup χ⟩

end StrictTwoGroups.TwoEquiv
namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv
universe u

/-- Equivariant boundary data with trivial object group need not satisfy Peiffer. -/
def trivialBoundary (H : Type u) [Group H] : CrossedModule.{u} where
  G := PUnit
  H := H
  τ := 1
  α := 1
  equivariant _ _ := by simp

theorem trivialBoundary_peiffer_iff (H : Type u) [Group H] :
    IsCrossedModule (trivialBoundary H) ↔ ∀ a b : H, a*b=b*a := by
  constructor
  · intro h a b
    have he := h a b
    change b=a*b*a⁻¹ at he
    exact ((eq_mul_inv_iff_mul_eq).mp he).symm
  · intro hc a b
    change b=a*b*a⁻¹
    apply (eq_mul_inv_iff_mul_eq).mpr
    exact (hc a b).symm

theorem nonabelian_trivial_boundary_not_crossed :
    ¬ IsCrossedModule (trivialBoundary (Equiv.Perm (Fin 3))) := by
  intro h
  exact permutations_do_not_commute ((trivialBoundary_peiffer_iff _).mp h p q)

theorem equivariance_alone_does_not_give_strict_group :
    ¬ IsStrictTwoGroup (toTwoGrp (trivialBoundary (Equiv.Perm (Fin 3)))) :=
  fun h => nonabelian_trivial_boundary_not_crossed (peiffer_of_toTwoGrp_strict _ h)

theorem abelian_trivial_boundary_is_strict (H : Type u) [CommGroup H] :
    IsStrictTwoGroup (toTwoGrp (trivialBoundary H)) :=
  toTwoGrp_isStrictTwoGroup _ ((trivialBoundary_peiffer_iff H).mpr (fun _ _ => mul_comm _ _))

end Queelius.StrictTwoGroups.Controls

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem S_map1_lawful {χ χ' : CrossedModule.{u}}
    (f : (χ.G → χ'.G) × (χ.H → χ'.H)) (hf : IsXModHom f) :
    IsTwoGrpHom (S.map1 f) := by
  let δ : χ.H →* χ'.H := MonoidHom.mk' f.2 hf.2.1
  refine ⟨hf.1,?_,?_,?_,?_⟩
  · intro x y
    apply SemidirectProduct.ext
    · change f.2 (x.left*χ.α x.right y.left)=f.2 x.left*χ'.α (f.1 x.right) (f.2 y.left)
      rw [hf.2.1,hf.2.2.2]
    · exact hf.1 _ _
  · intro x
    constructor
    · rfl
    · change χ'.τ (f.2 x.left)*f.1 x.right=f.1 (χ.τ x.left*x.right)
      rw [hf.2.2.1,hf.1]
  · intro g
    apply SemidirectProduct.ext
    · exact δ.map_one
    · rfl
  · intro a b hab
    apply SemidirectProduct.ext
    · exact hf.2.1 _ _
    · rfl

theorem crossed_naturality {χ χ' : CrossedModule.{u}} (hχ' : IsCrossedModule χ')
    (f g : (χ.G → χ'.G) × (χ.H → χ'.H)) (hf : IsXModHom f)
    (η : χ.G → χ'.H) (hη : IsXModTwoHom f g η) (h : χ.H) (x : χ.G) :
    η (χ.τ h*x)*f.2 h=g.2 h*η x := by
  rw [hη.1,hη.2.2,←hf.2.2.1,hχ']
  group

theorem S_map2_lawful {χ χ' : CrossedModule.{u}} (hχ' : IsCrossedModule χ')
    (f g : (χ.G → χ'.G) × (χ.H → χ'.H)) (hf : IsXModHom f)
    (η : χ.G → χ'.H) (hη : IsXModTwoHom f g η) :
    IsTwoGrpTwoHom (S.map1 f) (S.map1 g) (S.map2 f g η) := by
  refine ⟨?_,?_,?_⟩
  · intro x y
    apply SemidirectProduct.ext
    · exact hη.1 _ _
    · exact hf.1 _ _
  · intro x
    change χ.G at x
    constructor
    · rfl
    · change χ'.τ (η x)*f.1 x=g.1 x
      rw [hη.2.1]
      group
  · intro a
    apply SemidirectProduct.ext
    · exact crossed_naturality hχ' f g hf η hη a.left a.right
    · rfl

theorem crossed_horizontal_identity {χ χ' χ'' : CrossedModule.{u}} (hχ'' : IsCrossedModule χ'')
    (f g : (χ.G → χ'.G) × (χ.H → χ'.H))
    (f' g' : (χ'.G → χ''.G) × (χ'.H → χ''.H)) (hf' : IsXModHom f')
    (η : χ.G → χ'.H) (η' : χ'.G → χ''.H)
    (hη : IsXModTwoHom f g η) (hη' : IsXModTwoHom f' g' η') (x : χ.G) :
    g'.2 (η x)*η' (f.1 x)=η' (g.1 x)*f'.2 (η x) := by
  have he : χ'.τ (η x)*f.1 x=g.1 x := by rw [hη.2.1]; group
  have h := crossed_naturality hχ'' f' g' hf' η' hη' (η x) (f.1 x)
  rw [he] at h
  exact h.symm
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem S_isTwoFunctor : IsTwoFunctor S.{u} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact toTwoGrp_isStrictTwoGroup
  · intro χ χ' f hχ hχ' hf
    exact S_map1_lawful f hf
  · intro χ χ' f g η hχ hχ' hf hg hη
    exact S_map2_lawful hχ' f g hf η hη
  · intro χ χ' f hχ hχ' hf
    rfl
  · intro χ χ' f g h η φ hχ hχ' hf hg hh hη hφ
    rfl
  · intro χ χ' χ'' f g hχ hχ' hχ'' hf hg
    rfl
  · intro χ χ' χ'' f g f' g' η η' hχ hχ' hχ'' hf hg hf' hg' hη hη'
    funext x
    apply SemidirectProduct.ext
    · exact crossed_horizontal_identity hχ'' f g f' g' hf' η η' hη hη' x
    · rfl
  · intro χ hχ
    rfl
  · intro χ hχ
    rfl
end StrictTwoGroups.TwoEquiv
universe u
theorem sfunctor_solution : StrictTwoGroups.TwoEquiv.IsTwoFunctor StrictTwoGroups.TwoEquiv.S.{u} :=
  StrictTwoGroups.TwoEquiv.S_isTwoFunctor

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem kerProj_identity (G : StrictTwoGroup.{u}) (g : G.G0) : kerProj G (G.i g)=1 := by
  apply Subtype.ext
  simp [kerProj,G.s_i]

theorem kerProj_multiply (G : StrictTwoGroup.{u}) (a b : G.G1) :
    kerProj G (a*b)=kerProj G a * (MulAut.conjNormal.comp G.i) (G.s a) (kerProj G b) := by
  apply Subtype.ext
  simp only [kerProj,toXMod,Subgroup.coe_mul,MonoidHom.comp_apply,MulAut.conjNormal_apply,
    map_mul,mul_inv_rev]
  group

theorem kerProj_composite (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (hab : G.s a=G.t b) :
    kerProj G (G.comp a b)=kerProj G a*kerProj G b := by
  apply Subtype.ext
  change G.comp a b*(G.i (G.s (G.comp a b)))⁻¹=
    (a*(G.i (G.s a))⁻¹)*(b*(G.i (G.s b))⁻¹)
  rw [(hG.1 a b hab).1,proposition_comp_formula G hG a b hab]
  group

theorem T_map1_coe {G G' : StrictTwoGroup.{u}}
    (F : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) (h : ↥G.s.ker) :
    ((kerProj G' (F.2 h)) : G'.G1)=F.2 h := by
  let F0 : G.G0 →* G'.G0 := MonoidHom.mk' F.1 hF.1
  have hs : G'.s (F.2 h)=1 := by rw [(hF.2.2.1 h).1,h.property]; exact F0.map_one
  change F.2 h*(G'.i (G'.s (F.2 h)))⁻¹=F.2 h
  simp [hs]

theorem kerProj_map {G G' : StrictTwoGroup.{u}}
    (F : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) (a : G.G1) :
    kerProj G' (F.2 a)=(T.map1 F).2 (kerProj G a) := by
  let F1 : G.G1 →* G'.G1 := MonoidHom.mk' F.2 hF.2.1
  apply Subtype.ext
  change (kerProj G' (F.2 a):G'.G1)=(kerProj G' (F.2 (kerProj G a)):G'.G1)
  rw [T_map1_coe F hF]
  change F.2 a*(G'.i (G'.s (F.2 a)))⁻¹=F1 (a*(G.i (G.s a))⁻¹)
  rw [map_mul,map_inv,(hF.2.2.1 a).1]
  change F.2 a*(G'.i (F.1 (G.s a)))⁻¹=F.2 a*(F.2 (G.i (G.s a)))⁻¹
  rw [hF.2.2.2.1]

theorem T_map1_lawful {G G' : StrictTwoGroup.{u}}
    (F : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) :
    IsXModHom (T.map1 F) := by
  change (∀ x y : G.G0, F.1 (x*y)=F.1 x*F.1 y) ∧
    (∀ h k : ↥G.s.ker,kerProj G' (F.2 (h*k))=kerProj G' (F.2 h)*kerProj G' (F.2 k)) ∧
    (∀ h : ↥G.s.ker,G'.t (kerProj G' (F.2 h):G'.G1)=F.1 (G.t h)) ∧
    (∀ (g : G.G0) (h : ↥G.s.ker),
      kerProj G' (F.2 ((MulAut.conjNormal.comp G.i) g h))=
        (MulAut.conjNormal.comp G'.i) (F.1 g) (kerProj G' (F.2 h)))
  let F1 : G.G1 →* G'.G1 := MonoidHom.mk' F.2 hF.2.1
  refine ⟨hF.1,?_,?_,?_⟩
  · intro h k
    apply Subtype.ext
    calc
      _ = F.2 ((h:G.G1)*(k:G.G1)) := T_map1_coe F hF (h*k)
      _ = F.2 h*F.2 k := hF.2.1 _ _
      _ = _ := congrArg₂ (fun a b : G'.G1 => a*b) (T_map1_coe F hF h).symm (T_map1_coe F hF k).symm
  · intro h
    change G'.t (kerProj G' (F.2 h):G'.G1)=F.1 (G.t h)
    rw [T_map1_coe F hF]
    exact (hF.2.2.1 h).2
  · intro g h
    apply Subtype.ext
    change (kerProj G' (F.2 ((MulAut.conjNormal.comp G.i) g h)):G'.G1)=
      ((MulAut.conjNormal.comp G'.i) (F.1 g) (kerProj G' (F.2 h)):G'.G1)
    rw [T_map1_coe F hF]
    change F1 (G.i g*(h:G.G1)*(G.i g)⁻¹)=
      G'.i (F.1 g)*(kerProj G' (F.2 h):G'.G1)*(G'.i (F.1 g))⁻¹
    rw [map_mul,map_mul,map_inv,T_map1_coe F hF]
    change F.2 (G.i g)*F.2 h*(F.2 (G.i g))⁻¹=_
    rw [hF.2.2.2.1]
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem T_map2_lawful {G G' : StrictTwoGroup.{u}} (hG' : IsStrictTwoGroup G')
    (F E : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) (hE : IsTwoGrpHom E)
    (θ : G.G0 → G'.G1) (hθ : IsTwoGrpTwoHom F E θ) :
    IsXModTwoHom (T.map1 F) (T.map1 E) (T.map2 F E θ) := by
  change (∀ x y : G.G0,kerProj G' (θ (x*y))=
    kerProj G' (θ x)*(MulAut.conjNormal.comp G'.i) (F.1 x) (kerProj G' (θ y))) ∧
    (∀ x : G.G0,G'.t (kerProj G' (θ x):G'.G1)=E.1 x*(F.1 x)⁻¹) ∧
    (∀ h : ↥G.s.ker,kerProj G' (θ (G.t h))=kerProj G' (E.2 h)*(kerProj G' (F.2 h))⁻¹)
  refine ⟨?_,?_,?_⟩
  · intro x y
    change kerProj G' (θ (x*y))=kerProj G' (θ x)*(MulAut.conjNormal.comp G'.i) (F.1 x) (kerProj G' (θ y))
    rw [hθ.1,kerProj_multiply,(hθ.2.1 x).1]
  · intro x
    change G.G0 at x
    change G'.t (θ x*(G'.i (G'.s (θ x)))⁻¹)=E.1 x*(F.1 x)⁻¹
    rw [map_mul,map_inv,G'.t_i,(hθ.2.1 x).1,(hθ.2.1 x).2]
  · intro h
    change ↥G.s.ker at h
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,T_map1_coe F hF,T_map1_coe E hE]
    let θhom : G.G0 →* G'.G1 := MonoidHom.mk' θ hθ.1
    let E0 : G.G0 →* G'.G0 := MonoidHom.mk' E.1 hE.1
    have hθ1 : θ 1=1 := θhom.map_one
    have hEs : G'.s (E.2 h)=1 := by rw [(hE.2.2.1 h).1,h.property]; exact E0.map_one
    have hu : G'.comp (E.2 h) 1=E.2 h := by simpa [hEs] using (hG'.2.1 (E.2 h)).1
    have hn := hθ.2.2 (h:G.G1)
    rw [h.property,hθ1,hu] at hn
    have hc : G'.s (θ (G.t h))=G'.t (F.2 h) := (hθ.2.1 _).1.trans (hF.2.2.1 h).2.symm
    rw [proposition_comp_formula G' hG' _ _ hc] at hn
    exact (eq_mul_inv_iff_mul_eq).mpr hn
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem T_isTwoFunctor : IsTwoFunctor T.{u} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact toXMod_isCrossedModule
  · intro G G' F hG hG' hF
    exact T_map1_lawful F hF
  · intro G G' F E θ hG hG' hF hE hθ
    exact T_map2_lawful hG' F E hF hE θ hθ
  · intro G G' F hG hG' hF
    funext x
    exact kerProj_identity G' (F.1 x)
  · intro G G' F E K θ φ hG hG' hF hE hK hθ hφ
    funext x
    exact kerProj_composite G' hG' (φ x) (θ x) ((hφ.2.1 x).1.trans (hθ.2.1 x).2.symm)
  · intro G G' G'' F E hG hG' hG'' hF hE
    change StrictTwoGroup.{u} at G G' G''
    apply Prod.ext
    · rfl
    · funext h
      change ↥G.s.ker at h
      exact kerProj_map E hE (F.2 h)
  · intro G G' G'' F E F' E' θ θ' hG hG' hG'' hF hE hF' hE' hθ hθ'
    change StrictTwoGroup.{u} at G G' G''
    funext x
    change G.G0 at x
    have hn := hθ'.2.2 (θ x)
    rw [(hθ.2.1 x).1,(hθ.2.1 x).2] at hn
    change kerProj G'' (G''.comp (θ' (E.1 x)) (F'.2 (θ x)))=
      kerProj G'' (E'.2 (kerProj G' (θ x)))*kerProj G'' (θ' (F.1 x))
    rw [hn]
    have hc : G''.s (E'.2 (θ x))=G''.t (θ' (F.1 x)) := by
      rw [(hE'.2.2.1 (θ x)).1,(hθ.2.1 x).1,(hθ'.2.1 (F.1 x)).2]
    rw [kerProj_composite G'' hG'' _ _ hc,kerProj_map E' hE']
    rfl
  · intro G hG
    change StrictTwoGroup.{u} at G
    apply Prod.ext
    · rfl
    · funext h
      change ↥G.s.ker at h
      apply Subtype.ext
      change (h:G.G1)*(G.i (G.s h))⁻¹=(h:G.G1)
      have hh : G.s (h:G.G1)=1 := h.property
      rw [hh]
      simp
  · intro G hG
    funext x
    exact kerProj_identity G x
end StrictTwoGroups.TwoEquiv

end

section
namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv

/-- In a lawful pair groupoid, the kernel coordinate is a cocycle, not a group morphism. -/
theorem kernel_projection_not_multiplicative :
    let G := pairGroupoid (Equiv.Perm (Fin 3))
    let a : G.G1 := (1,q)
    let b : G.G1 := (p,1)
    kerProj G (a*b) ≠ kerProj G a*kerProj G b := by
  dsimp only
  intro h
  have hh := congrArg (fun k : ↥(pairGroupoid (Equiv.Perm (Fin 3))).s.ker => k.val.1) h
  change p*q⁻¹=q⁻¹*p at hh
  have hn : (p*q⁻¹ : Equiv.Perm (Fin 3)) ≠ q⁻¹*p := by decide
  exact hn hh

/-- Multiplication of already-kernel arrows needs no twisting. -/
theorem kernel_projection_on_kernel (G : StrictTwoGroup) (h : ↥G.s.ker) :
    kerProj G h=h := by
  apply Subtype.ext
  have hh : G.s (h:G.G1)=1 := h.property
  change (h:G.G1)*(G.i (G.s h))⁻¹=(h:G.G1)
  rw [hh]
  simp
end Queelius.StrictTwoGroups.Controls

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem hom_from_structural_maps {G G' : StrictTwoGroup.{u}}
    (hG : IsStrictTwoGroup G) (hG' : IsStrictTwoGroup G')
    (F : (G.G0→G'.G0)×(G.G1→G'.G1))
    (h0 : ∀x y,F.1 (x*y)=F.1 x*F.1 y) (h1 : ∀a b,F.2 (a*b)=F.2 a*F.2 b)
    (hs : ∀a,G'.s (F.2 a)=F.1 (G.s a)) (ht : ∀a,G'.t (F.2 a)=F.1 (G.t a))
    (hi : ∀g,F.2 (G.i g)=G'.i (F.1 g)) : IsTwoGrpHom F := by
  refine ⟨h0,h1,fun a=>⟨hs a,ht a⟩,hi,?_⟩
  intro a b hab
  let F1 : G.G1→*G'.G1:=MonoidHom.mk' F.2 h1
  have hab' : G'.s (F.2 a)=G'.t (F.2 b) := by rw [hs,ht,hab]
  rw [proposition_comp_formula G hG a b hab,proposition_comp_formula G' hG' _ _ hab']
  change F1 (a*(G.i (G.s a))⁻¹*b)=F.2 a*(G'.i (G'.s (F.2 a)))⁻¹*F.2 b
  rw [map_mul,map_mul,map_inv]
  change F.2 a*(F.2 (G.i (G.s a)))⁻¹*F.2 b=_
  rw [hi,hs]

def xiInverse (G : StrictTwoGroup.{u}) : twoGrp.Hom1 G ((T.comp S).obj G) :=
  (id,sourceSplit G)

theorem xi_lawful (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G) : IsTwoGrpHom (xi G) := by
  have hST:=toTwoGrp_isStrictTwoGroup (toXMod G) (toXMod_isCrossedModule G hG)
  apply hom_from_structural_maps hST hG
  · intro x y; rfl
  · intro a b
    exact (sourceSplit G).symm.map_mul a b
  · intro a
    change (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0) at a
    change G.s ((a.left:G.G1)*G.i a.right)=a.right
    rw [map_mul,a.left.property,G.s_i,one_mul]
  · intro a
    change (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0) at a
    change G.t ((a.left:G.G1)*G.i a.right)=G.t a.left*a.right
    rw [map_mul,G.t_i]
  · intro g
    change (1:G.G1)*G.i g=G.i g
    exact one_mul _

theorem xi_inverse_lawful (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G) :
    IsTwoGrpHom (xiInverse G) := by
  have hST:=toTwoGrp_isStrictTwoGroup (toXMod G) (toXMod_isCrossedModule G hG)
  apply hom_from_structural_maps hG hST
  · intro x y; rfl
  · intro a b; exact (sourceSplit G).map_mul a b
  · intro a; rfl
  · intro a
    change G.t (a*(G.i (G.s a))⁻¹)*G.s a=G.t a
    rw [map_mul,map_inv,G.t_i]
    group
  · intro g
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change (G.i g*(G.i (G.s (G.i g)))⁻¹)=1
      simp [G.s_i]
    · exact G.s_i g

theorem xi_inverse_identities (G : StrictTwoGroup.{u}) :
    twoGrp.comp1 (xi G) (xiInverse G)=twoGrp.id1 ((T.comp S).obj G) ∧
      twoGrp.comp1 (xiInverse G) (xi G)=twoGrp.id1 G := by
  constructor
  · apply Prod.ext
    · rfl
    · funext a
      exact (sourceSplit G).apply_symm_apply a
  · apply Prod.ext
    · rfl
    · funext a
      exact (sourceSplit G).symm_apply_apply a
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem xi_natural_one {G G' : StrictTwoGroup.{u}}
    (F : (G.G0→G'.G0)×(G.G1→G'.G1)) (hF : IsTwoGrpHom F) :
    twoGrp.comp1 ((T.comp S).map1 F) (xi G')=
      twoGrp.comp1 (xi G) ((Raw2Functor.id twoGrp).map1 F) := by
  apply Prod.ext
  · rfl
  · funext a
    change (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0) at a
    change ((kerProj G' (F.2 a.left)):G'.G1)*G'.i (F.1 a.right)=F.2 ((a.left:G.G1)*G.i a.right)
    rw [T_map1_coe F hF,hF.2.1,hF.2.2.2.1]

theorem xi_natural_two {G G' : StrictTwoGroup.{u}} (hG' : IsStrictTwoGroup G')
    (F E : (G.G0→G'.G0)×(G.G1→G'.G1)) (hF : IsTwoGrpHom F)
    (θ : G.G0→G'.G1) (hθ : IsTwoGrpTwoHom F E θ) :
    twoGrp.hcomp ((T.comp S).map1 F) ((T.comp S).map1 E) (xi G') (xi G')
      ((T.comp S).map2 F E θ) (twoGrp.id2 (xi G'))=
      twoGrp.hcomp (xi G) (xi G) F E (twoGrp.id2 (xi G)) θ := by
  funext x
  change G.G0 at x
  change G'.comp (G'.i (E.1 x)) ((kerProj G' (θ x):G'.G1)*G'.i (F.1 x))=
    G'.comp (θ x) (F.2 (G.i x))
  have hr : (kerProj G' (θ x):G'.G1)*G'.i (F.1 x)=θ x := by
    change (θ x*(G'.i (G'.s (θ x)))⁻¹)*G'.i (F.1 x)=θ x
    rw [(hθ.2.1 x).1]
    group
  rw [hr,hF.2.2.2.1,←(hθ.2.1 x).2,←(hθ.2.1 x).1]
  exact (hG'.2.1 (θ x)).2.trans (hG'.2.1 (θ x)).1.symm

theorem xi_isTwoNatIso : IsTwoNatIso (T.comp S) (Raw2Functor.id twoGrp.{u}) xi := by
  refine ⟨?_,?_,?_⟩
  · intro G hG
    exact ⟨xi_lawful G hG,xiInverse G,xi_inverse_lawful G hG,xi_inverse_identities G⟩
  · intro G G' F hG hG' hF
    exact xi_natural_one F hF
  · intro G G' F E θ hG hG' hF hE hθ
    exact xi_natural_two hG' F E hF θ hθ
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem kernel_semidirect_right (χ : CrossedModule.{u}) (h : ↥(toTwoGrp χ).s.ker) :
    (h.val:χ.H⋊[χ.α]χ.G).right=1 := h.property

def kernelEmbedding (χ : CrossedModule.{u}) (h : χ.H) : ↥(toTwoGrp χ).s.ker :=
  ⟨SemidirectProduct.inl h,by change (1:χ.G)=1; rfl⟩

theorem semidirect_left_mul_of_right_one {H G : Type u} [Group H] [Group G]
    (φ : G →* MulAut H) (a b : H⋊[φ]G) (ha : a.right=1) :
    (a*b).left=a.left*b.left := by
  simp [SemidirectProduct.mul_left,ha]

def kernelSemidirectEquiv (χ : CrossedModule.{u}) : ↥(toTwoGrp χ).s.ker≃*χ.H where
  toFun h:=(h.val:χ.H⋊[χ.α]χ.G).left
  invFun := kernelEmbedding χ
  left_inv h:=by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact (kernel_semidirect_right χ h).symm
  right_inv h:=rfl
  map_mul' h k:=semidirect_left_mul_of_right_one χ.α h.val k.val h.property

theorem kernel_projection_left (χ : CrossedModule.{u}) (x : χ.H⋊[χ.α]χ.G) :
    ((kerProj (toTwoGrp χ) x).val : χ.H⋊[χ.α]χ.G).left=x.left := by
  change (x*(SemidirectProduct.inr x.right)⁻¹).left=x.left
  simp [SemidirectProduct.mul_left]

theorem conjugation_inr_left (χ : CrossedModule.{u}) (g : χ.G) (h : χ.H⋊[χ.α]χ.G) :
    (SemidirectProduct.inr g*h*(SemidirectProduct.inr g)⁻¹).left=χ.α g h.left := by
  simp [SemidirectProduct.mul_left]
theorem semidirect_inl_action (χ : CrossedModule.{u}) (g : χ.G) (h : χ.H) :
    (SemidirectProduct.inl (χ.α g h):χ.H⋊[χ.α]χ.G)=
      SemidirectProduct.inr g*SemidirectProduct.inl h*(SemidirectProduct.inr g)⁻¹ := by
  apply SemidirectProduct.ext <;> simp [SemidirectProduct.mul_left]
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

def zetaInverse (χ : CrossedModule.{u}) : xMod.Hom1 χ ((S.comp T).obj χ) :=
  (id,kernelEmbedding χ)

theorem zeta_lawful (χ : CrossedModule.{u}) : IsXModHom (zeta χ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y; rfl
  · intro h k
    exact (kernelSemidirectEquiv χ).map_mul h k
  · intro h
    change ↥(toTwoGrp χ).s.ker at h
    change χ.τ (h.val:χ.H⋊[χ.α]χ.G).left=χ.τ (h.val:χ.H⋊[χ.α]χ.G).left*(h.val:χ.H⋊[χ.α]χ.G).right
    rw [kernel_semidirect_right,mul_one]
  · intro g h
    change χ.G at g
    change ↥(toTwoGrp χ).s.ker at h
    exact conjugation_inr_left χ g h.val

theorem zeta_inverse_lawful (χ : CrossedModule.{u}) : IsXModHom (zetaInverse χ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y; rfl
  · intro h k
    exact (kernelSemidirectEquiv χ).symm.map_mul h k
  · intro h
    change χ.τ h*1=χ.τ h
    exact mul_one _
  · intro g h
    apply Subtype.ext
    exact semidirect_inl_action χ g h

theorem zeta_inverse_identities (χ : CrossedModule.{u}) :
    xMod.comp1 (zeta χ) (zetaInverse χ)=xMod.id1 ((S.comp T).obj χ) ∧
      xMod.comp1 (zetaInverse χ) (zeta χ)=xMod.id1 χ := by
  constructor
  · apply Prod.ext
    · rfl
    · funext h
      exact (kernelSemidirectEquiv χ).symm_apply_apply h
  · rfl

theorem zeta_natural_one {χ χ' : CrossedModule.{u}}
    (f : (χ.G→χ'.G)×(χ.H→χ'.H)) :
    xMod.comp1 ((S.comp T).map1 f) (zeta χ')=
      xMod.comp1 (zeta χ) ((Raw2Functor.id xMod).map1 f) := by
  apply Prod.ext
  · rfl
  · funext h
    change ↥(toTwoGrp χ).s.ker at h
    change ((kerProj (toTwoGrp χ') ((S.map1 f).2 h.val)).val:χ'.H⋊[χ'.α]χ'.G).left=
      f.2 (h.val:χ.H⋊[χ.α]χ.G).left
    exact kernel_projection_left χ' _

theorem zeta_natural_two {χ χ' : CrossedModule.{u}}
    (f g : (χ.G→χ'.G)×(χ.H→χ'.H)) (hg : IsXModHom g) (η : χ.G→χ'.H) :
    xMod.hcomp ((S.comp T).map1 f) ((S.comp T).map1 g) (zeta χ') (zeta χ')
      ((S.comp T).map2 f g η) (xMod.id2 (zeta χ'))=
      xMod.hcomp (zeta χ) (zeta χ) f g (xMod.id2 (zeta χ)) η := by
  let δ : χ.H→*χ'.H:=MonoidHom.mk' g.2 hg.2.1
  funext x
  change χ.G at x
  change ((kerProj (toTwoGrp χ') (⟨η x,f.1 x⟩:χ'.H⋊[χ'.α]χ'.G)).val:χ'.H⋊[χ'.α]χ'.G).left*1=
    δ 1*η x
  rw [kernel_projection_left,δ.map_one,mul_one,one_mul]

theorem zeta_isTwoNatIso : IsTwoNatIso (S.comp T) (Raw2Functor.id xMod.{u}) zeta := by
  refine ⟨?_,?_,?_⟩
  · intro χ hχ
    exact ⟨zeta_lawful χ,zetaInverse χ,zeta_inverse_lawful χ,zeta_inverse_identities χ⟩
  · intro χ χ' f hχ hχ' hf
    exact zeta_natural_one f
  · intro χ χ' f g η hχ hχ' hf hg hη
    exact zeta_natural_two f g hg η
end StrictTwoGroups.TwoEquiv

end

section
namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv
universe u

/-- The kernel part alone cannot reconstruct an arrow; the source coordinate matters. -/
theorem kernel_part_loses_source (G : StrictTwoGroup.{u}) (g : G.G0) (hg : g≠1) :
    G.i g≠1 ∧ kerProj G (G.i g)=kerProj G 1 := by
  constructor
  · intro h
    have hs:=congrArg G.s h
    rw [G.s_i,map_one] at hs
    exact hg hs
  · rw [kerProj_identity]
    apply Subtype.ext
    simp [kerProj]

/-- The inverse used by zeta reconstructs the kernel, not arbitrary semidirect elements. -/
theorem left_part_loses_base (χ : CrossedModule.{u}) (g : χ.G) (hg : g≠1) :
    (SemidirectProduct.inl (SemidirectProduct.inr g : χ.H⋊[χ.α]χ.G).left : χ.H⋊[χ.α]χ.G)≠
      SemidirectProduct.inr g := by
  intro h
  have hr:=congrArg (fun x : χ.H⋊[χ.α]χ.G=>x.right) h
  exact hg hr.symm
end Queelius.StrictTwoGroups.Controls

end

section
universe u
theorem roundtrip_solution :
    StrictTwoGroups.TwoEquiv.IsTwoNatIso
      (StrictTwoGroups.TwoEquiv.T.comp StrictTwoGroups.TwoEquiv.S)
      (StrictTwoGroups.TwoEquiv.Raw2Functor.id StrictTwoGroups.TwoEquiv.twoGrp.{u})
      StrictTwoGroups.TwoEquiv.xi :=
  StrictTwoGroups.TwoEquiv.xi_isTwoNatIso

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem twoGrp_id_lawful (A : StrictTwoGroup.{u}) : IsTwoGrpHom (twoGrp.id1 A) := by
  exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _=>⟨rfl,rfl⟩,fun _=>rfl,fun _ _ _=>rfl⟩

theorem twoGrp_comp_lawful {A B C : StrictTwoGroup.{u}}
    (F : (A.G0→B.G0)×(A.G1→B.G1)) (G : (B.G0→C.G0)×(B.G1→C.G1))
    (hF : IsTwoGrpHom F) (hG : IsTwoGrpHom G) : IsTwoGrpHom (twoGrp.comp1 F G) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x y; change G.1 (F.1 (x*y))=_; rw [hF.1,hG.1]; rfl
  · intro x y; change G.2 (F.2 (x*y))=_; rw [hF.2.1,hG.2.1]; rfl
  · intro a
    exact ⟨by change C.s (G.2 (F.2 a))=_; rw [(hG.2.2.1 _).1,(hF.2.2.1 _).1]; rfl,
      by change C.t (G.2 (F.2 a))=_; rw [(hG.2.2.1 _).2,(hF.2.2.1 _).2]; rfl⟩
  · intro x; change G.2 (F.2 (A.i x))=_; rw [hF.2.2.2.1,hG.2.2.2.1]; rfl
  · intro a b hab
    change G.2 (F.2 (A.comp a b))=_
    rw [hF.2.2.2.2 a b hab,hG.2.2.2.2 _ _ (by rw [(hF.2.2.1 _).1,(hF.2.2.1 _).2,hab])]
    rfl

theorem twoGrp_id2_lawful {A B : StrictTwoGroup.{u}} (hB : IsStrictTwoGroup B)
    (F : (A.G0→B.G0)×(A.G1→B.G1)) (hF : IsTwoGrpHom F) :
    IsTwoGrpTwoHom F F (twoGrp.id2 F) := by
  refine ⟨?_,?_,?_⟩
  · intro x y; change B.i (F.1 (x*y))=_; rw [hF.1,map_mul]; rfl
  · intro x; exact ⟨B.s_i _,B.t_i _⟩
  · intro a
    change B.comp (B.i (F.1 (A.t a))) (F.2 a)=B.comp (F.2 a) (B.i (F.1 (A.s a)))
    rw [←(hF.2.2.1 a).1,←(hF.2.2.1 a).2,(hB.2.1 _).1,(hB.2.1 _).2]

theorem twoGrp_vertical_lawful {A B : StrictTwoGroup.{u}} (hB : IsStrictTwoGroup B)
    (F G H : (A.G0→B.G0)×(A.G1→B.G1))
    (hF : IsTwoGrpHom F) (hG : IsTwoGrpHom G) (hH : IsTwoGrpHom H)
    (θ φ : A.G0→B.G1) (hθ : IsTwoGrpTwoHom F G θ) (hφ : IsTwoGrpTwoHom G H φ) :
    IsTwoGrpTwoHom F H (twoGrp.vcomp F G H θ φ) := by
  have hc (x : A.G0) : B.s (φ x)=B.t (θ x) := (hφ.2.1 x).1.trans (hθ.2.1 x).2.symm
  refine ⟨?_,?_,?_⟩
  · intro x y
    change B.comp (φ (x*y)) (θ (x*y))=_
    rw [hφ.1,hθ.1,hB.2.2.2 _ _ _ _ (hc x) (hc y)]
    rfl
  · intro x
    obtain ⟨hs,ht⟩:=hB.1 (φ x) (θ x) (hc x)
    exact ⟨hs.trans (hθ.2.1 x).1,ht.trans (hφ.2.1 x).2⟩
  · intro a
    have ht : B.s (θ (A.t a))=B.t (F.2 a) := (hθ.2.1 _).1.trans (hF.2.2.1 _).2.symm
    have hg : B.s (φ (A.t a))=B.t (G.2 a) := (hφ.2.1 _).1.trans (hG.2.2.1 _).2.symm
    have gs : B.s (G.2 a)=B.t (θ (A.s a)) := (hG.2.2.1 _).1.trans (hθ.2.1 _).2.symm
    have hs : B.s (H.2 a)=B.t (φ (A.s a)) := (hH.2.2.1 _).1.trans (hφ.2.1 _).2.symm
    change B.comp (B.comp (φ (A.t a)) (θ (A.t a))) (F.2 a)=
      B.comp (H.2 a) (B.comp (φ (A.s a)) (θ (A.s a)))
    calc
      _=B.comp (φ (A.t a)) (B.comp (θ (A.t a)) (F.2 a)) := hB.2.2.1 _ _ _ (hc _) ht
      _=B.comp (φ (A.t a)) (B.comp (G.2 a) (θ (A.s a))) := by rw [hθ.2.2 a]
      _=B.comp (B.comp (φ (A.t a)) (G.2 a)) (θ (A.s a)) := (hB.2.2.1 _ _ _ hg gs).symm
      _=B.comp (B.comp (H.2 a) (φ (A.s a))) (θ (A.s a)) := by rw [hφ.2.2 a]
      _=_ := hB.2.2.1 _ _ _ hs (hc _)

theorem twoGrp_prewhisker_lawful {A B C : StrictTwoGroup.{u}}
    (F : (A.G0→B.G0)×(A.G1→B.G1)) (G H : (B.G0→C.G0)×(B.G1→C.G1))
    (hF : IsTwoGrpHom F) (θ : B.G0→C.G1) (hθ : IsTwoGrpTwoHom G H θ) :
    IsTwoGrpTwoHom (twoGrp.comp1 F G) (twoGrp.comp1 F H) (fun x=>θ (F.1 x)) := by
  refine ⟨?_,fun x=>hθ.2.1 (F.1 x),?_⟩
  · intro x y; change θ (F.1 (x*y))=_; rw [hF.1,hθ.1]
  · intro a
    have h:=hθ.2.2 (F.2 a)
    rw [(hF.2.2.1 _).1,(hF.2.2.1 _).2] at h
    exact h

theorem twoGrp_postwhisker_lawful {A B C : StrictTwoGroup.{u}}
    (F G : (A.G0→B.G0)×(A.G1→B.G1)) (H : (B.G0→C.G0)×(B.G1→C.G1))
    (hF : IsTwoGrpHom F) (hG : IsTwoGrpHom G) (hH : IsTwoGrpHom H)
    (θ : A.G0→B.G1) (hθ : IsTwoGrpTwoHom F G θ) :
    IsTwoGrpTwoHom (twoGrp.comp1 F H) (twoGrp.comp1 G H) (fun x=>H.2 (θ x)) := by
  refine ⟨?_,?_,?_⟩
  · intro x y; change H.2 (θ (x*y))=_; rw [hθ.1,hH.2.1]
  · intro x
    exact ⟨by rw [(hH.2.2.1 _).1,(hθ.2.1 _).1]; rfl,
      by rw [(hH.2.2.1 _).2,(hθ.2.1 _).2]; rfl⟩
  · intro a
    have h:=congrArg H.2 (hθ.2.2 a)
    rw [hH.2.2.2.2 _ _ ((hθ.2.1 _).1.trans (hF.2.2.1 _).2.symm),
      hH.2.2.2.2 _ _ ((hG.2.2.1 _).1.trans (hθ.2.1 _).2.symm)] at h
    exact h

theorem twoGrp_horizontal_lawful {A B C : StrictTwoGroup.{u}} (hC : IsStrictTwoGroup C)
    (F G : (A.G0→B.G0)×(A.G1→B.G1)) (F' G' : (B.G0→C.G0)×(B.G1→C.G1))
    (hF : IsTwoGrpHom F) (hG : IsTwoGrpHom G) (hF' : IsTwoGrpHom F') (hG' : IsTwoGrpHom G')
    (θ : A.G0→B.G1) (θ' : B.G0→C.G1) (hθ : IsTwoGrpTwoHom F G θ) (hθ' : IsTwoGrpTwoHom F' G' θ') :
    IsTwoGrpTwoHom (twoGrp.comp1 F F') (twoGrp.comp1 G G') (twoGrp.hcomp F G F' G' θ θ') := by
  exact twoGrp_vertical_lawful hC _ _ _ (twoGrp_comp_lawful F F' hF hF')
    (twoGrp_comp_lawful G F' hG hF') (twoGrp_comp_lawful G G' hG hG') _ _
    (twoGrp_postwhisker_lawful F G F' hF hG hF' θ hθ)
    (twoGrp_prewhisker_lawful G F' G' hG θ' hθ')
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem comp_middle_exchange (C : StrictTwoGroup.{u}) (hC : IsStrictTwoGroup C)
    (a b c d e f : C.G1)
    (hab : C.s a=C.t b) (hbc : C.s b=C.t c) (hcd : C.s c=C.t d)
    (hae : C.s a=C.t e) (hef : C.s e=C.t f) (hfd : C.s f=C.t d)
    (he : C.comp b c=C.comp e f) :
    C.comp (C.comp a b) (C.comp c d)=C.comp (C.comp a e) (C.comp f d) := by
  calc
    _=C.comp (C.comp (C.comp a b) c) d := (hC.2.2.1 _ _ _ ((hC.1 _ _ hab).1.trans hbc) hcd).symm
    _=C.comp (C.comp a (C.comp b c)) d := by rw [hC.2.2.1 a b c hab hbc]
    _=C.comp (C.comp a (C.comp e f)) d := by rw [he]
    _=C.comp (C.comp (C.comp a e) f) d := by rw [hC.2.2.1 a e f hae hef]
    _=_ := hC.2.2.1 _ _ _ ((hC.1 _ _ hae).1.trans hef) hfd

theorem twoGrp_interchange {A B C : StrictTwoGroup.{u}} (hC : IsStrictTwoGroup C)
    (F G H : (A.G0→B.G0)×(A.G1→B.G1)) (F' G' H' : (B.G0→C.G0)×(B.G1→C.G1))
    (hF' : IsTwoGrpHom F') (hG' : IsTwoGrpHom G')
    (θ φ : A.G0→B.G1) (θ' φ' : B.G0→C.G1)
    (hθ : IsTwoGrpTwoHom F G θ) (hφ : IsTwoGrpTwoHom G H φ)
    (hθ' : IsTwoGrpTwoHom F' G' θ') (hφ' : IsTwoGrpTwoHom G' H' φ') :
    twoGrp.hcomp F H F' H' (twoGrp.vcomp F G H θ φ) (twoGrp.vcomp F' G' H' θ' φ')=
      twoGrp.vcomp (twoGrp.comp1 F F') (twoGrp.comp1 G G') (twoGrp.comp1 H H')
        (twoGrp.hcomp F G F' G' θ θ') (twoGrp.hcomp G H G' H' φ φ') := by
  funext x
  change C.comp (C.comp (φ' (H.1 x)) (θ' (H.1 x))) (F'.2 (B.comp (φ x) (θ x)))=
    C.comp (C.comp (φ' (H.1 x)) (G'.2 (φ x))) (C.comp (θ' (G.1 x)) (F'.2 (θ x)))
  rw [hF'.2.2.2.2 _ _ ((hφ.2.1 x).1.trans (hθ.2.1 x).2.symm)]
  apply comp_middle_exchange C hC
  · exact (hφ'.2.1 _).1.trans (hθ'.2.1 _).2.symm
  · rw [(hθ'.2.1 _).1,(hF'.2.2.1 _).2,(hφ.2.1 _).2]
  · rw [(hF'.2.2.1 _).1,(hF'.2.2.1 _).2,(hφ.2.1 _).1,(hθ.2.1 _).2]
  · rw [(hφ'.2.1 _).1,(hG'.2.2.1 _).2,(hφ.2.1 _).2]
  · rw [(hG'.2.2.1 _).1,(hθ'.2.1 _).2,(hφ.2.1 _).1]
  · rw [(hθ'.2.1 _).1,(hF'.2.2.1 _).2,(hθ.2.1 _).2]
  · have h:=hθ'.2.2 (φ x)
    rwa [(hφ.2.1 _).1,(hφ.2.1 _).2] at h

theorem twoGrp_horizontal_assoc {A B C D : StrictTwoGroup.{u}} (hD : IsStrictTwoGroup D)
    (F G : (A.G0→B.G0)×(A.G1→B.G1)) (F' G' : (B.G0→C.G0)×(B.G1→C.G1))
    (F'' G'' : (C.G0→D.G0)×(C.G1→D.G1)) (hF' : IsTwoGrpHom F') (hF'' : IsTwoGrpHom F'')
    (θ : A.G0→B.G1) (θ' : B.G0→C.G1) (θ'' : C.G0→D.G1)
    (hθ : IsTwoGrpTwoHom F G θ) (hθ' : IsTwoGrpTwoHom F' G' θ') (hθ'' : IsTwoGrpTwoHom F'' G'' θ'') :
    twoGrp.hcomp (twoGrp.comp1 F F') (twoGrp.comp1 G G') F'' G'' (twoGrp.hcomp F G F' G' θ θ') θ''=
      twoGrp.hcomp F G (twoGrp.comp1 F' F'') (twoGrp.comp1 G' G'') θ (twoGrp.hcomp F' G' F'' G'' θ' θ'') := by
  funext x
  change D.comp (θ'' (G'.1 (G.1 x))) (F''.2 (C.comp (θ' (G.1 x)) (F'.2 (θ x))))=
    D.comp (D.comp (θ'' (G'.1 (G.1 x))) (F''.2 (θ' (G.1 x)))) (F''.2 (F'.2 (θ x)))
  have hc : C.s (θ' (G.1 x))=C.t (F'.2 (θ x)) := by
    rw [(hθ'.2.1 _).1,(hF'.2.2.1 _).2,(hθ.2.1 _).2]
  rw [hF''.2.2.2.2 _ _ hc]
  symm
  apply hD.2.2.1
  · rw [(hθ''.2.1 _).1,(hF''.2.2.1 _).2,(hθ'.2.1 _).2]
  · rw [(hF''.2.2.1 _).1,(hF''.2.2.1 _).2,hc]

theorem twoGrp_isStrict2Category : Raw2Cat.IsStrict2Category twoGrp.{u} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro A _; exact twoGrp_id_lawful A
  · intro A B C F G _ _ _ hF hG; exact twoGrp_comp_lawful F G hF hG
  · intro A B F _ hB hF; exact twoGrp_id2_lawful hB F hF
  · intro A B F G H θ φ _ hB hF hG hH hθ hφ
    exact twoGrp_vertical_lawful hB F G H hF hG hH θ φ hθ hφ
  · intro A B C F G F' G' θ θ' _ _ hC hF hG hF' hG' hθ hθ'
    exact twoGrp_horizontal_lawful hC F G F' G' hF hG hF' hG' θ θ' hθ hθ'
  · intro A B F G θ _ hB _ _ hθ
    constructor <;> funext x
    · change B.comp (θ x) (B.i (F.1 x))=θ x
      rw [←(hθ.2.1 x).1]; exact (hB.2.1 _).1
    · change B.comp (B.i (G.1 x)) (θ x)=θ x
      rw [←(hθ.2.1 x).2]; exact (hB.2.1 _).2
  · intro A B F G H K θ φ ψ _ hB _ _ _ _ hθ hφ hψ
    funext x
    exact (hB.2.2.1 (ψ x) (φ x) (θ x) ((hψ.2.1 _).1.trans (hφ.2.1 _).2.symm)
      ((hφ.2.1 _).1.trans (hθ.2.1 _).2.symm)).symm
  · intro A B C F F' _ _ hC _ hF'
    funext x
    change C.comp (C.i (F'.1 (F.1 x))) (F'.2 (B.i (F.1 x)))=C.i (F'.1 (F.1 x))
    rw [hF'.2.2.2.1]
    simpa only [C.s_i] using (hC.2.1 (C.i (F'.1 (F.1 x)))).1
  · intro A B C F G H F' G' H' θ φ θ' φ' _ _ hC _ _ _ hF' hG' _ hθ hφ hθ' hφ'
    exact twoGrp_interchange hC F G H F' G' H' hF' hG' θ φ θ' φ' hθ hφ hθ' hφ'
  · intro A B C D F F' F'' _ _ _ _ _ _ _; rfl
  · intro A B C D F G F' G' F'' G'' θ θ' θ'' _ _ _ hD _ _ hF' _ hF'' _ hθ hθ' hθ''
    exact twoGrp_horizontal_assoc hD F G F' G' F'' G'' hF' hF'' θ θ' θ'' hθ hθ' hθ''
  · intro A B F _ _ _; exact ⟨rfl,rfl⟩
  · intro A B F G θ _ hB hF _ hθ
    constructor <;> funext x
    · change B.comp (θ x) (F.2 (A.i x))=θ x
      rw [hF.2.2.2.1,←(hθ.2.1 x).1]
      exact (hB.2.1 _).1
    · change B.comp (B.i (G.1 x)) (θ x)=θ x
      rw [←(hθ.2.1 x).2]
      exact (hB.2.1 _).2
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem xMod_id_lawful (A : CrossedModule.{u}) : IsXModHom (xMod.id1 A) := by
  exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _ _=>rfl⟩

theorem xMod_comp_lawful {A B C : CrossedModule.{u}}
    (f : (A.G→B.G)×(A.H→B.H)) (g : (B.G→C.G)×(B.H→C.H))
    (hf : IsXModHom f) (hg : IsXModHom g) : IsXModHom (xMod.comp1 f g) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y; change g.1 (f.1 (x*y))=_; rw [hf.1,hg.1]; rfl
  · intro x y; change g.2 (f.2 (x*y))=_; rw [hf.2.1,hg.2.1]; rfl
  · intro h; change C.τ (g.2 (f.2 h))=_; rw [hg.2.2.1,hf.2.2.1]; rfl
  · intro x h; change g.2 (f.2 (A.α x h))=_; rw [hf.2.2.2,hg.2.2.2]; rfl

/-- The semidirect-product 2-cell encoding reflects all three crossed-module laws. -/
theorem S_map2_reflect {A B : CrossedModule.{u}}
    (f g : (A.G→B.G)×(A.H→B.H)) (hf : IsXModHom f) (η : A.G→B.H)
    (hη : IsTwoGrpTwoHom (S.map1 f) (S.map1 g) (S.map2 f g η)) : IsXModTwoHom f g η := by
  have hder (x y : A.G) : η (x*y)=η x*B.α (f.1 x) (η y) :=
    congrArg SemidirectProduct.left (hη.1 x y)
  let f0 : A.G→*B.G := MonoidHom.mk' f.1 hf.1
  have hf1 : f.1 1=1 := f0.map_one
  have hone : η 1=1 := by
    have h:=hder 1 1
    rw [one_mul,hf1,map_one] at h
    change η 1=η 1*η 1 at h
    exact mul_eq_left.mp h.symm
  refine ⟨hder,?_,?_⟩
  · intro x
    have h:=(hη.2.1 x).2
    change B.τ (η x)*f.1 x=g.1 x at h
    exact eq_mul_inv_of_mul_eq h
  · intro h
    have hn:=congrArg SemidirectProduct.left (hη.2.2 (SemidirectProduct.inl h))
    change η (A.τ h*1)*f.2 h=g.2 h*η 1 at hn
    rw [mul_one,hone,mul_one] at hn
    exact eq_mul_inv_of_mul_eq hn

theorem xMod_id2_lawful {A B : CrossedModule.{u}}
    (f : (A.G→B.G)×(A.H→B.H)) : IsXModTwoHom f f (xMod.id2 f) := by
  refine ⟨?_,?_,?_⟩
  · intro x y; change (1:B.H)=1*B.α (f.1 x) 1; simp
  · intro x; change B.τ 1=f.1 x*(f.1 x)⁻¹; simp
  · intro h; change (1:B.H)=f.2 h*(f.2 h)⁻¹; simp

theorem xMod_vertical_lawful {A B : CrossedModule.{u}} (hB : IsCrossedModule B)
    (f g h : (A.G→B.G)×(A.H→B.H)) (hf : IsXModHom f) (hg : IsXModHom g) (hh : IsXModHom h)
    (η φ : A.G→B.H) (hη : IsXModTwoHom f g η) (hφ : IsXModTwoHom g h φ) :
    IsXModTwoHom f h (xMod.vcomp f g h η φ) := by
  apply S_map2_reflect f h hf
  exact twoGrp_vertical_lawful (toTwoGrp_isStrictTwoGroup B hB) _ _ _
    (S_map1_lawful f hf) (S_map1_lawful g hg) (S_map1_lawful h hh) _ _
    (S_map2_lawful hB f g hf η hη) (S_map2_lawful hB g h hg φ hφ)

theorem xMod_horizontal_lawful {A B C : CrossedModule.{u}} (hB : IsCrossedModule B) (hC : IsCrossedModule C)
    (f g : (A.G→B.G)×(A.H→B.H)) (f' g' : (B.G→C.G)×(B.H→C.H))
    (hf : IsXModHom f) (hg : IsXModHom g) (hf' : IsXModHom f') (hg' : IsXModHom g')
    (η : A.G→B.H) (η' : B.G→C.H) (hη : IsXModTwoHom f g η) (hη' : IsXModTwoHom f' g' η') :
    IsXModTwoHom (xMod.comp1 f f') (xMod.comp1 g g') (xMod.hcomp f g f' g' η η') := by
  apply S_map2_reflect _ _ (xMod_comp_lawful f f' hf hf')
  have he : S.map2 (xMod.comp1 f f') (xMod.comp1 g g') (xMod.hcomp f g f' g' η η')=
      twoGrp.hcomp (S.map1 f) (S.map1 g) (S.map1 f') (S.map1 g') (S.map2 f g η) (S.map2 f' g' η') := by
    funext x
    apply SemidirectProduct.ext
    · exact crossed_horizontal_identity hC f g f' g' hf' η η' hη hη' x
    · rfl
  rw [he]
  exact twoGrp_horizontal_lawful (toTwoGrp_isStrictTwoGroup C hC) _ _ _ _
    (S_map1_lawful f hf) (S_map1_lawful g hg) (S_map1_lawful f' hf') (S_map1_lawful g' hg') _ _
    (S_map2_lawful hB f g hf η hη) (S_map2_lawful hC f' g' hf' η' hη')
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem xMod_interchange {A B C : CrossedModule.{u}} (hC : IsCrossedModule C)
    (f g h : (A.G→B.G)×(A.H→B.H)) (f' g' h' : (B.G→C.G)×(B.H→C.H))
    (hg' : IsXModHom g') (hh' : IsXModHom h')
    (η φ : A.G→B.H) (η' φ' : B.G→C.H)
    (hη : IsXModTwoHom f g η) (hφ' : IsXModTwoHom g' h' φ') :
    xMod.hcomp f h f' h' (xMod.vcomp f g h η φ) (xMod.vcomp f' g' h' η' φ')=
      xMod.vcomp (xMod.comp1 f f') (xMod.comp1 g g') (xMod.comp1 h h')
        (xMod.hcomp f g f' g' η η') (xMod.hcomp g h g' h' φ φ') := by
  funext x
  change h'.2 (φ x*η x)*(φ' (f.1 x)*η' (f.1 x))=
    (h'.2 (φ x)*φ' (g.1 x))*(g'.2 (η x)*η' (f.1 x))
  rw [hh'.2.1]
  have he:=crossed_horizontal_identity hC f g g' h' hg' η φ' hη hφ' x
  calc
    _=h'.2 (φ x)*(h'.2 (η x)*φ' (f.1 x))*η' (f.1 x) := by group
    _=_ := by rw [he]; group

theorem xMod_horizontal_assoc {A B C D : CrossedModule.{u}}
    (f g : (A.G→B.G)×(A.H→B.H)) (f' g' : (B.G→C.G)×(B.H→C.H))
    (f'' g'' : (C.G→D.G)×(C.H→D.H)) (hg'' : IsXModHom g'')
    (η : A.G→B.H) (η' : B.G→C.H) (η'' : C.G→D.H) :
    xMod.hcomp (xMod.comp1 f f') (xMod.comp1 g g') f'' g'' (xMod.hcomp f g f' g' η η') η''=
      xMod.hcomp f g (xMod.comp1 f' f'') (xMod.comp1 g' g'') η (xMod.hcomp f' g' f'' g'' η' η'') := by
  funext x
  change g''.2 (g'.2 (η x)*η' (f.1 x))*η'' (f'.1 (f.1 x))=
    g''.2 (g'.2 (η x))*(g''.2 (η' (f.1 x))*η'' (f'.1 (f.1 x)))
  rw [hg''.2.1,mul_assoc]

theorem xMod_isStrict2Category : Raw2Cat.IsStrict2Category xMod.{u} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro A _; exact xMod_id_lawful A
  · intro A B C f g _ _ _ hf hg; exact xMod_comp_lawful f g hf hg
  · intro A B f _ _ _; exact xMod_id2_lawful f
  · intro A B f g h η φ _ hB hf hg hh hη hφ
    exact xMod_vertical_lawful hB f g h hf hg hh η φ hη hφ
  · intro A B C f g f' g' η η' _ hB hC hf hg hf' hg' hη hη'
    exact xMod_horizontal_lawful hB hC f g f' g' hf hg hf' hg' η η' hη hη'
  · intro A B f g η _ _ _ _ _
    change CrossedModule.{u} at A B
    constructor <;> funext x
    · exact mul_one _
    · exact one_mul _
  · intro A B f g h k η φ ψ _ _ _ _ _ _ _ _ _
    change CrossedModule.{u} at A B
    funext x
    exact (mul_assoc (ψ x) (φ x) (η x)).symm
  · intro A B C f f' _ _ _ _ hf'
    change CrossedModule.{u} at A B C
    funext x
    change f'.2 1*1=(1:C.H)
    let h : B.H→*C.H := MonoidHom.mk' f'.2 hf'.2.1
    rw [mul_one]
    exact h.map_one
  · intro A B C f g h f' g' h' η φ η' φ' _ _ hC _ _ _ _ hg' hh' hη _ _ hφ'
    exact xMod_interchange hC f g h f' g' h' hg' hh' η φ η' φ' hη hφ'
  · intro A B C D f f' f'' _ _ _ _ _ _ _; rfl
  · intro A B C D f g f' g' f'' g'' η η' η'' _ _ _ _ _ _ _ _ _ hg'' _ _ _
    exact xMod_horizontal_assoc f g f' g' f'' g'' hg'' η η' η''
  · intro A B f _ _ _; exact ⟨rfl,rfl⟩
  · intro A B f g η _ _ _ hg _
    change CrossedModule.{u} at A B
    constructor <;> funext x
    · change g.2 1*η x=η x
      let h : A.H→*B.H := MonoidHom.mk' g.2 hg.2.1
      have he : g.2 1=1 := h.map_one
      rw [he,one_mul]
    · exact mul_one _

/-- Both strict 2-category structures, both functors and both two-sided natural isomorphisms. -/
theorem theorem_two_equivalence : TwoEquivalent twoGrp.{u} xMod.{u} := by
  exact ⟨twoGrp_isStrict2Category,xMod_isStrict2Category,T,S,xi,zeta,
    T_isTwoFunctor,S_isTwoFunctor,xi_isTwoNatIso,zeta_isTwoNatIso⟩
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem crossed_twohom_one {A B : CrossedModule.{u}}
    (f g : (A.G→B.G)×(A.H→B.H)) (hf : IsXModHom f) (η : A.G→B.H)
    (hη : IsXModTwoHom f g η) : η 1=1 := by
  let f0 : A.G→*B.G := MonoidHom.mk' f.1 hf.1
  have hf1 : f.1 1=1 := f0.map_one
  have h:=hη.1 1 1
  rw [one_mul,hf1,map_one] at h
  change η 1=η 1*η 1 at h
  exact mul_eq_left.mp h.symm

theorem S_map2_lawful_iff {A B : CrossedModule.{u}} (hB : IsCrossedModule B)
    (f g : (A.G→B.G)×(A.H→B.H)) (hf : IsXModHom f) (η : A.G→B.H) :
    IsTwoGrpTwoHom (S.map1 f) (S.map1 g) (S.map2 f g η) ↔ IsXModTwoHom f g η :=
  ⟨S_map2_reflect f g hf η,S_map2_lawful hB f g hf η⟩

theorem S_map1_injective {A B : CrossedModule.{u}} :
    Function.Injective (@S.map1 A B) := by
  intro f g he
  apply Prod.ext
  · exact congrArg (fun F : (A.G→B.G)×((A.H ⋊[A.α] A.G)→(B.H ⋊[B.α] B.G)) => F.1) he
  · funext h
    exact congrArg (fun F : (A.G→B.G)×((A.H ⋊[A.α] A.G)→(B.H ⋊[B.α] B.G)) =>
      (F.2 (SemidirectProduct.inl h)).left) he

theorem S_map2_injective {A B : CrossedModule.{u}}
    (f g : (A.G→B.G)×(A.H→B.H)) : Function.Injective (S.map2 f g) := by
  intro η φ he
  funext x
  exact congrArg SemidirectProduct.left (congrFun he x)
end StrictTwoGroups.TwoEquiv

namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv
universe u

/-- A nonidentity constant cannot be a lawful crossed-module 2-cell. -/
theorem nonidentity_constant_not_twohom {A B : CrossedModule.{u}}
    (f g : (A.G→B.G)×(A.H→B.H)) (hf : IsXModHom f) (h : B.H) (hn : h≠1) :
    ¬IsXModTwoHom f g (fun _=>h) := by
  intro hη
  exact hn (crossed_twohom_one f g hf _ hη)
end Queelius.StrictTwoGroups.Controls

end

section
universe audit_u0
theorem submission_primary_solution :
StrictTwoGroups.TwoEquiv.TwoEquivalent StrictTwoGroups.TwoEquiv.twoGrp StrictTwoGroups.TwoEquiv.xMod := @StrictTwoGroups.TwoEquiv.theorem_two_equivalence

end

universe audit_u0

theorem solution : (
  StrictTwoGroups.TwoEquiv.Raw2Cat.IsStrict2Category StrictTwoGroups.TwoEquiv.twoGrp
) := @StrictTwoGroups.TwoEquiv.twoGrp_isStrict2Category
