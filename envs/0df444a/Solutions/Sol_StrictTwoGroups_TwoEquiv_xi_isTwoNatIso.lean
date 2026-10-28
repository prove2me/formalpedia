-- Prove2me | solution 1 for StrictTwoGroups.TwoEquiv.xi_isTwoNatIso
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:59.406205+00:00
-- url     : https://prove2.me/submissions/5b3e3d9d-6e76-4f87-a755-1d2efbed1303

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
theorem solution :
    StrictTwoGroups.TwoEquiv.IsTwoNatIso
      (StrictTwoGroups.TwoEquiv.T.comp StrictTwoGroups.TwoEquiv.S)
      (StrictTwoGroups.TwoEquiv.Raw2Functor.id StrictTwoGroups.TwoEquiv.twoGrp.{u})
      StrictTwoGroups.TwoEquiv.xi :=
  StrictTwoGroups.TwoEquiv.xi_isTwoNatIso

end
