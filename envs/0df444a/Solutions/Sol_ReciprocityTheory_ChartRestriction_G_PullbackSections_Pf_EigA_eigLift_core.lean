-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.eigLift_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:06.488597+00:00
-- url     : https://prove2.me/submissions/0607e8eb-fba4-4597-b234-de5517aeab77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_OactH_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_hset_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_hset_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_idem_eig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gauge_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_betaH_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_betaH_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_beta_sesquilinear


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [Field k]
    [Algebra ℚ k] [Algebra R k] (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h)
    {L Ty : Type} (ty : L → Ty) (χ : Ty → O →+* k) (u : L → Fin d → R)
    (heig : ∀ ℓ a, (dAct k B a).mulVec (fun i => algebraMap R k (u ℓ i)) =
      χ (ty ℓ) a • fun i => algebraMap R k (u ℓ i))
    (hidem : ∀ t : Ty, ∃ (n : ℕ) (b : Fin n → O) (c : Fin n → R), (∑ i, algebraMap R k (c i) * χ t (b i) = 1) ∧
      ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap R k (c i) = χ t a * algebraMap R k (c j)) :
    ∃ φ : L → Fin d → R, ∀ ℓ ℓ', (∃ a, χ (ty ℓ) a ≠ χ (ty ℓ') (star a)) →
      ∑ i, (algebraMap R k (φ ℓ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by
  classical
  have key : ∀ ℓ' : L, ∃ φ' : Fin d → R, ∀ ℓ : L, (∃ a, χ (ty ℓ) a ≠ χ (ty ℓ') (star a)) →
      ∑ i, (algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by
    intro ℓ'
    obtain ⟨n, b, c, hnorm, hm⟩ := hidem (ty ℓ')
    set U : Fin d → k := fun i => algebraMap R k (u ℓ' i) with hUdef
    set ξ0 : (Fin d → k) × (Fin d → k) := (U, -(sg1 k h).mulVec U) with hξ0def
    set ξ1 : (Fin d → k) × (Fin d → k) :=
      ((∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U,
        (∑ i, algebraMap R k (c i) • dActS k B (b i)).mulVec (-(sg1 k h).mulVec U)) with hξ1def
    have hξ0 : ξ0 ∈ Hset (R := R) k h := ⟨u ℓ', 0, Prod.ext rfl (by funext i; simp [hξ0def, hUdef])⟩
    have hsum : ξ1 = ∑ i, algebraMap R k (c i) • OactH k B (b i) ξ0 := by
      refine Prod.ext ?_ ?_
      · simp only [hξ1def, hξ0def, Prod.fst_sum, Prod.smul_fst, OactH_eq, Matrix.sum_mulVec, Matrix.smul_mulVec]
      · simp only [hξ1def, hξ0def, Prod.snd_sum, Prod.smul_snd, OactH_eq, Matrix.sum_mulVec, Matrix.smul_mulVec]
    have hξ1 : ξ1 ∈ Hset (R := R) k h := by
      rw [hsum]
      exact hset_sum k h _ _ fun i _ => hset_smul k h (c i) (gauge_stable R d O k hRQ B h hc (b i) ξ0 hξ0)
    have hfirst : (∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U = U := by
      have he : ∀ i, (dActH k B (b i)).mulVec U = χ (ty ℓ') (b i) • U := fun i => heig ℓ' (b i)
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, he, smul_smul]
      rw [← Finset.sum_smul, hnorm, one_smul]
    obtain ⟨u1, φ1, hu1⟩ := hξ1
    have hU1 : (fun j => algebraMap R k (u1 j)) = U := by
      have h1 := congrArg Prod.fst hu1
      exact h1.symm.trans hfirst
    refine ⟨φ1, fun ℓ hℓ => ?_⟩
    obtain ⟨a, ha⟩ := hℓ
    obtain ⟨m, hb, hcm⟩ := hm (star a)
    have heigξ : OactH k B (star a) ξ1 = χ (ty ℓ') (star a) • ξ1 := by
      rw [OactH_eq]
      refine Prod.ext ?_ ?_
      · show (dActH k B (star a)).mulVec ((∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U) =
          χ (ty ℓ') (star a) • (∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U
        rw [Matrix.mulVec_mulVec, idem_eig (dActH k B) (χ (ty ℓ')) b (fun i => algebraMap R k (c i)) (star a) m hb hcm,
          Matrix.smul_mulVec]
      · show (dActS k B (star a)).mulVec ((∑ i, algebraMap R k (c i) • dActS k B (b i)).mulVec (-(sg1 k h).mulVec U)) =
          χ (ty ℓ') (star a) • (∑ i, algebraMap R k (c i) • dActS k B (b i)).mulVec (-(sg1 k h).mulVec U)
        rw [Matrix.mulVec_mulVec, idem_eig (dActS k B) (χ (ty ℓ')) b (fun i => algebraMap R k (c i)) (star a) m hb hcm,
          Matrix.smul_mulVec]
    have hv : OactH k B a ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) =
        χ (ty ℓ) a • ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) := by
      rw [OactH_eq]
      refine Prod.ext ?_ ?_
      · exact heig ℓ a
      · simp
    have hs := beta_sesquilinear R d O k B a ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) ξ1
    rw [hv, heigξ, betaH_smul_left, betaH_smul_right] at hs
    have hβ : betaH k ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) ξ1 = 0 := by
      have h2 : (χ (ty ℓ) a - χ (ty ℓ') (star a)) * betaH k ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) ξ1 = 0 := by
        rw [sub_mul, hs, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
    rw [hu1] at hβ
    simp only [betaH, Pi.zero_apply, zero_mul, sub_zero] at hβ
    rw [hU1] at hβ
    exact hβ
  choose φ hφ using key
  exact ⟨φ, fun ℓ ℓ' hℓ => hφ ℓ' ℓ hℓ⟩
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
