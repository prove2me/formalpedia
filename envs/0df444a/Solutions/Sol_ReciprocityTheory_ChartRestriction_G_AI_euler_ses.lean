-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.euler_ses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:30.463616+00:00
-- url     : https://prove2.me/submissions/c171882c-6933-4da6-9e2d-be819e05ed6b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_six_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A : Type*} [CommRing A] {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M'']
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (x : A) :
    length A (LinearMap.ker (LinearMap.lsmul A M' x)) + length A (LinearMap.ker (LinearMap.lsmul A M'' x)) +
        length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        length A (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)) +
        length A (M'' ⧸ LinearMap.range (LinearMap.lsmul A M'' x)) := by
  have key : ∀ z : LinearMap.ker (LinearMap.lsmul A M'' x), ∃ (m : M) (m' : M'),
      g m = (z : M'') ∧ f m' = x • m := by
    intro z
    obtain ⟨m, hm⟩ := hg z
    have hz : x • (z : M'') = 0 := z.2
    obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hz])
    exact ⟨m, m', hm, hm'⟩
  have indep : ∀ (m₁ : M) (m₁' : M') (m₂ : M) (m₂' : M'), g m₁ = g m₂ → f m₁' = x • m₁ →
      f m₂' = x • m₂ →
      Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₁' =
        Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₂' := by
    intro m₁ m₁' m₂ m₂' h h1 h2
    obtain ⟨n, hn⟩ := (hex (m₁ - m₂)).1 (by rw [map_sub, h, sub_self])
    have e : m₁' - m₂' = x • n := hf (by rw [map_sub, map_smul, hn, h1, h2, smul_sub])
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, e]
    exact ⟨n, rfl⟩
  choose lift liftP hlift using key
  obtain ⟨δ, hδ⟩ : ∃ δ : LinearMap.ker (LinearMap.lsmul A M'' x) →ₗ[A]
      (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)),
      ∀ (z : LinearMap.ker (LinearMap.lsmul A M'' x)) (m : M) (m' : M'), g m = (z : M'') → f m' = x • m →
        δ z = Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m' := by
    refine ⟨{ toFun := fun z => Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) (liftP z),
              map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro z₁ z₂
      show Submodule.mkQ _ (liftP (z₁ + z₂)) = Submodule.mkQ _ (liftP z₁) + Submodule.mkQ _ (liftP z₂)
      rw [← map_add]
      exact indep _ _ (lift z₁ + lift z₂) _
        (by rw [(hlift _).1, map_add, (hlift z₁).1, (hlift z₂).1, Submodule.coe_add]) (hlift _).2
        (by rw [map_add, (hlift z₁).2, (hlift z₂).2, smul_add])
    · intro a z
      show Submodule.mkQ _ (liftP (a • z)) = a • Submodule.mkQ _ (liftP z)
      rw [← map_smul]
      exact indep _ _ (a • lift z) _
        (by rw [(hlift _).1, map_smul, (hlift z).1, Submodule.coe_smul]) (hlift _).2
        (by rw [map_smul, (hlift z).2, smul_comm])
    · intro z m m' h h'
      exact indep _ _ m m' (by rw [(hlift z).1, h]) (hlift z).2 h'
  have h₁ : Function.Injective (kerSmulMap f x) := by
    intro a b h
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val h
  have h₂ : Function.Exact (kerSmulMap f x) (kerSmulMap g x) := by
    intro y
    constructor
    · intro hy
      have hy0 : g y = 0 := congrArg Subtype.val hy
      obtain ⟨m', hm'⟩ := (hex y).1 hy0
      have hyx : x • (y : M) = 0 := y.2
      refine ⟨⟨m', ?_⟩, Subtype.ext hm'⟩
      show x • m' = 0
      apply hf
      rw [map_smul, hm', hyx, map_zero]
    · rintro ⟨w, rfl⟩
      apply Subtype.ext
      exact (hex _).2 ⟨w, rfl⟩
  have h₃ : Function.Exact (kerSmulMap g x) δ := by
    intro z
    constructor
    · intro hz
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [hδ z m m' hm hm', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨n, hn⟩ := LinearMap.mem_range.1 hz
      have hn' : x • n = m' := hn
      refine ⟨⟨m - f n, ?_⟩, Subtype.ext ?_⟩
      · show x • (m - f n) = 0
        rw [smul_sub, ← map_smul, hn', hm', sub_self]
      · show g (m - f n) = z
        rw [map_sub, hm, (hex _).2 ⟨n, rfl⟩, sub_zero]
    · rintro ⟨y, rfl⟩
      have hyx : x • (y : M) = 0 := y.2
      rw [hδ _ y 0 rfl (by rw [map_zero, hyx]), map_zero]
  have h₄ : Function.Exact δ (cokerSmulMap f x) := by
    intro w
    obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m = f m' := hm
      refine ⟨⟨g m, ?_⟩, hδ _ m m' rfl hm2.symm⟩
      show x • g m = 0
      rw [← map_smul, hm2]
      exact (hex _).2 ⟨m', rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨n', hn'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [← hz, hδ z m n' hm hn']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f n') = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hn']
      exact ⟨m, rfl⟩
  have h₅ : Function.Exact (cokerSmulMap f x) (cokerSmulMap g x) := by
    intro w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g m) = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m'', hm''⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m'' = g m := hm''
      obtain ⟨t, ht⟩ := hg m''
      obtain ⟨m', hm'⟩ := (hex (m - x • t)).1 (by rw [map_sub, map_smul, ht, hm2, sub_self])
      refine ⟨Submodule.mkQ _ m', ?_⟩
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = Submodule.mkQ _ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hm']
      refine ⟨-t, ?_⟩
      show x • -t = m - x • t - m
      rw [smul_neg]
      abel
    · rintro ⟨w', hw'⟩
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w'
      rw [← hw']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g (f m')) = 0
      rw [(hex _).2 ⟨m', rfl⟩, map_zero]
  have h₆ : Function.Surjective (cokerSmulMap g x) := by
    intro w
    obtain ⟨m'', rfl⟩ := Submodule.mkQ_surjective _ w
    obtain ⟨m, rfl⟩ := hg m''
    exact ⟨Submodule.mkQ _ m, rfl⟩
  exact length_six_term h₁ h₂ h₃ h₄ h₅ h₆
end ReciprocityTheory.ChartRestriction.G.AI
