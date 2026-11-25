-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.beta_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:26.837542+00:00
-- url     : https://prove2.me/submissions/1bf8308e-5afa-4c82-b58d-e2f81d38857d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_eig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_actP_actP_eig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_betaH_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_betaH_sum_right

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (B : FB R d O) {Ty : Type} [Fintype Ty] (χ : Ty → O →+* k) (nt : Ty → ℕ)
    (bt : ∀ t, Fin (nt t) → O) (ct : ∀ t, Fin (nt t) → k) (heq : ∀ t, IsEqv (χ t) (bt t) (ct t))
    (hcompH : ∑ t, actD (EigA.dActH k B) (bt t) (ct t) = 1) (hcompS : ∑ t, actD (EigA.dActS k B) (bt t) (ct t) = 1)
    {n n' : ℕ} (bz : Fin n → O) (cz : Fin n → k) (bw : Fin n' → O) (cw : Fin n' → k) (ξ0 η0 : (Fin d → k) × (Fin d → k))
    (hsep : ∀ t t', evD (χ t) bz cz ≠ 0 → evD (χ t') bw cw ≠ 0 → ∃ a, χ t a ≠ χ t' (star a)) :
    betaH k (actP B bz cz ξ0) (actP B bw cw η0) = 0 := by
  classical
  have hsmulL : ∀ (e : k) (x y : (Fin d → k) × (Fin d → k)),
      betaH k (e • x) y = e * betaH k x y := by
    intro e x y
    simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsmulR : ∀ (e : k) (x y : (Fin d → k) × (Fin d → k)),
      betaH k x (e • y) = e * betaH k x y := by
    intro e x y
    simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmv : ∀ (A : Matrix (Fin d) (Fin d) k) (v : Fin d → k) (i : Fin d),
      A.mulVec v i = ∑ j, A i j * v j := fun A v i => rfl
  have hadj : ∀ (a : O) (x y : (Fin d → k) × (Fin d → k)),
      betaH k (OactH k B a x) y = betaH k x (OactH k B (star a) y) := by
    intro a x y
    simp only [betaH, OactH, star_star, hmv, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have horth : ∀ (t t' : Ty) (x y : (Fin d → k) × (Fin d → k)), (∃ a, χ t a ≠ χ t' (star a)) →
      betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) = 0 := by
    intro t t' x y ⟨a, ha⟩
    have h1 : betaH k (OactH k B a (actP B (bt t) (ct t) x)) (actP B (bt t') (ct t') y) =
        χ t a * betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) := by
      rw [actP_eig B (χ t) (bt t) (ct t) (heq t) x a, hsmulL]
    have h2 : betaH k (actP B (bt t) (ct t) x) (OactH k B (star a) (actP B (bt t') (ct t') y)) =
        χ t' (star a) * betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) := by
      rw [actP_eig B (χ t') (bt t') (ct t') (heq t') y (star a), hsmulR]
    rw [hadj] at h1
    rw [h1] at h2
    have h3 : (χ t a - χ t' (star a)) *
        betaH k (actP B (bt t) (ct t) x) (actP B (bt t') (ct t') y) = 0 := by
      rw [sub_mul, h2, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha)
  have hs : ∀ (s : Finset Ty) (N : Ty → Matrix (Fin d) (Fin d) k) (v : Fin d → k),
      (∑ t ∈ s, N t).mulVec v = ∑ t ∈ s, (N t).mulVec v := by
    intro s N v
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih]
  have hdec : ∀ x : (Fin d → k) × (Fin d → k), x = ∑ t, actP B (bt t) (ct t) x := by
    intro x
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact calc x.1 = (1 : Matrix (Fin d) (Fin d) k).mulVec x.1 := (Matrix.one_mulVec _).symm
        _ = (∑ t, actD (EigA.dActH k B) (bt t) (ct t)).mulVec x.1 := by rw [hcompH]
        _ = ∑ t, (actD (EigA.dActH k B) (bt t) (ct t)).mulVec x.1 := hs _ _ _
    · rw [Prod.snd_sum]
      exact calc x.2 = (1 : Matrix (Fin d) (Fin d) k).mulVec x.2 := (Matrix.one_mulVec _).symm
        _ = (∑ t, actD (EigA.dActS k B) (bt t) (ct t)).mulVec x.2 := by rw [hcompS]
        _ = ∑ t, (actD (EigA.dActS k B) (bt t) (ct t)).mulVec x.2 := hs _ _ _
  rw [hdec (actP B bz cz ξ0), hdec (actP B bw cw η0), betaH_sum_left]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [betaH_sum_right]
  refine Finset.sum_eq_zero fun t' _ => ?_
  rw [actP_actP_eig B (χ t) (bt t) (ct t) (heq t) bz cz ξ0,
    actP_actP_eig B (χ t') (bt t') (ct t') (heq t') bw cw η0, hsmulL, hsmulR]
  by_cases hz : evD (χ t) bz cz = 0
  · rw [hz, zero_mul]
  by_cases hw : evD (χ t') bw cw = 0
  · rw [hw, zero_mul, mul_zero]
  rw [horth t t' ξ0 η0 (hsep t t' hz hw), mul_zero, mul_zero]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
