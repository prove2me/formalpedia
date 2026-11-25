-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.aeval_trv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:57:56.07502+00:00
-- url     : https://prove2.me/submissions/2e107bc8-18c0-4106-afd6-348ee8e31862

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_transvection_fix_generator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : S) :
    aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) F0 = aeval r F0 := by

  set ev : Polynomial (MvPolynomial (TVar d.D d.N) K) →+* S :=
    Polynomial.eval₂RingHom (aeval r : MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom b with hev
  have hcomp : ev.comp (trv (R := K) i k Polynomial.X).toRingHom =
      (aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) :
        MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hev, trv]
    · intro t
      by_cases h1 : t.1 = i <;> simp [hev, trv, h1] <;> ring
  have h := congrArg (fun φ => φ F0) hcomp
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
  rw [← h, transvection_fix_generator d c F0 hF0 hker i k hik]
  simp [hev]
end ReciprocityTheory.ChartRestriction.G.T0.Data
