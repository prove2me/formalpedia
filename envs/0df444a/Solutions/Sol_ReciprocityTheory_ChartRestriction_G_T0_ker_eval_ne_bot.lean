-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ker_eval_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:29.532132+00:00
-- url     : https://prove2.me/submissions/e3f54458-997a-47c5-9775-178a892b69df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (hΩ : Algebra.trdeg K Ω = D) (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    kerP (K := K) (D := D) j₀ x ≠ ⊥ := by
  intro hbot
  have hinj : Function.Injective (chiP (K := K) (D := D) j₀ x) :=
    (RingHom.injective_iff_ker_eq_bot (chiP (K := K) (D := D) j₀ x).toRingHom).mpr hbot
  have hphi : MvPolynomial.aeval (fun i : TVar D N => chiP (K := K) (D := D) j₀ x (MvPolynomial.X i)) =
      chiP (K := K) (D := D) j₀ x := by
    first
    | (ext i; simp)
    | exact (MvPolynomial.aeval_unique _).symm
  have hind : AlgebraicIndependent K
      (fun i : TVar D N => chiP (K := K) (D := D) j₀ x (MvPolynomial.X i)) := by
    rw [algebraicIndependent_iff_injective_aeval, hphi]
    exact hinj
  have h1 := hind.cardinalMk_le_trdeg
  have h2 : Algebra.trdeg K Ω + Algebra.trdeg Ω (MvPolynomial (Fin (D + 1) × Fin N) Ω) =
      Algebra.trdeg K (MvPolynomial (Fin (D + 1) × Fin N) Ω) := trdeg_add_eq K Ω
  rw [← h2, MvPolynomial.trdeg_of_isDomain, hΩ, Cardinal.mk_fintype, Cardinal.mk_fintype,
    Cardinal.lift_natCast] at h1
  have h3 : Fintype.card (TVar D N) ≤ D + Fintype.card (Fin (D + 1) × Fin N) := by exact_mod_cast h1
  simp only [TVar, Fintype.card_prod, Fintype.card_fin] at h3
  have h4 : (D + 1) * (N + 1) = (D + 1) * N + (D + 1) := by ring
  linarith
end ReciprocityTheory.ChartRestriction.G.T0
