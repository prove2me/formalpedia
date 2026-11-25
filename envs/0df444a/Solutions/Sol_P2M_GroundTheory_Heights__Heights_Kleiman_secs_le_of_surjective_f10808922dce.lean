-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_secs_le_of_surjective_f10808922dce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:29.80824+00:00
-- url     : https://prove2.me/submissions/9c8f2e54-00a2-4f49-a7d2-bed649db0288

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locRes_locRes_d12e0af235a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locRes_self_fe16e7a28657
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locRes_mem_degLoc_397295d09ee9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_rep_of_mem_twistMod_1bc86b616455
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMod_quot_eq_zero_1dfdbf1c2e89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locRes_rep_eq_ba90a5b4aacc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isHomogeneous_of_isWeightedHomogeneous_one_b668b222bb4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_quotGraded_piece_498792b22d20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hy : y ≠ 0) (n : ℕ)
    (hsurj : Function.Surjective (toH0 (primeQuotGraded (S := S) y) (n : ℤ))) :
    (twistSys S y (n : ℤ)).secs ≤ (coordGraded S y).piece (n : ℤ) := by
  intro z hz
  have hloc : ∀ j : Fin (N + 1), ∃ w : LocMod S N (Poly S N ⧸ primeOf (S := S) y) {j},
      w ∈ degLoc (primeQuotGraded (S := S) y) (n : ℤ)
        ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ ∧
      ∀ _ : y j ≠ 0, ∃ (g s : Poly S N) (e : ℕ) (hs : s ∈ monos ({j} : Finset (Fin (N + 1)))),
        s.IsHomogeneous e ∧ g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s ∧
        w = LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩ := by
    intro j
    by_cases hj : y j = 0
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd hj h⟩
    · have hzj : z ∈ twistMod S y (n : ℤ) (singleChart hj) := by
        have h' := hz
        simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at h'
        exact h' (singleChart hj)
      obtain ⟨g, s, e, hs, hse, hg, hgz⟩ := exists_rep_of_mem_twistMod y n hj hzj
      refine ⟨LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩,
        Submodule.subset_span ⟨Ideal.Quotient.mk (primeOf (S := S) y) g, ⟨s, hs⟩, ((e + n : ℕ) : ℤ), e,
          mem_quotGraded_piece.mpr ⟨g, isWeightedHomogeneous_int_of_isHomogeneous hg, rfl⟩, hse,
          by push_cast; ring, rfl⟩,
        fun _ => ⟨g, s, e, hs, hse, hg, hgz, rfl⟩⟩
  choose w hwdeg hwrep using hloc
  have hcompat : ∀ (J : Finset (Fin (N + 1))) (a b : Fin (N + 1)) (ha : a ∈ J) (hb : b ∈ J),
      locRes (Finset.singleton_subset_iff.mpr ha) (w a) =
        locRes (Finset.singleton_subset_iff.mpr hb) (w b) := by
    intro J a b ha hb
    by_cases h0 : ∃ i ∈ J, y i = 0
    · obtain ⟨i, hi, hyi⟩ := h0
      rw [locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr ha) (w a)),
        locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr hb) (w b))]
    · push Not at h0
      obtain ⟨ga, sa, ea, hsa, hsae, hga, hza, hwa⟩ := hwrep a (h0 a ha)
      obtain ⟨gb, sb, eb, hsb, hsbe, hgb, hzb, hwb⟩ := hwrep b (h0 b hb)
      rw [hwa, hwb]
      exact locRes_rep_eq y ha hb ga sa gb sb ea eb hsa hsb hsae hsbe hga hgb hza hzb
  let v : ∀ I : StdCell N, LocMod S N (Poly S N ⧸ primeOf (S := S) y) I.1 := fun I =>
    locRes (Finset.singleton_subset_iff.mpr (I.1.min'_mem I.2.1)) (w (I.1.min' I.2.1))
  have hv : ∀ (I : StdCell N) (a : Fin (N + 1)) (ha : a ∈ I.1),
      v I = locRes (Finset.singleton_subset_iff.mpr ha) (w a) :=
    fun I a ha => hcompat I.1 _ a (I.1.min'_mem I.2.1) ha
  have hvres : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J := by
    intro I J h
    change locRes h (v I) = v J
    obtain ⟨a, ha⟩ := I.2.1
    rw [hv I a ha, hv J a (h ha), locRes_locRes]
  let ζ : Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0 := fun I => v I.1
  have hζ : ζ ∈ Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
      (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0 := by
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr
      (Cech.d_zero_of_compat (G := locSys S N (Poly S N ⧸ primeOf (S := S) y)) (ρ := locResS) v hvres), ?_⟩
    rw [Cech.Cdeg, Submodule.mem_pi]
    intro I _
    obtain ⟨a, ha⟩ := I.1.2.1
    change v I.1 ∈ _
    rw [hv I.1 a ha]
    exact locRes_mem_degLoc _ _ ⟨{a}, Finset.singleton_nonempty a, Finset.subset_univ _⟩ I.1 _ (hwdeg a)
  obtain ⟨m, hm⟩ := hsurj (Submodule.Quotient.mk ⟨ζ, hζ⟩)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have heq : constCochain (m : Poly S N ⧸ primeOf (S := S) y) = ζ := by
    change Submodule.Quotient.mk (⟨constCochain (m : Poly S N ⧸ primeOf (S := S) y),
      constCochain_mem _ _ _ m.2⟩ : Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
        (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0) = _ at hm
    have h2 := (Submodule.Quotient.eq _).mp hm
    rw [Submodule.mem_comap] at h2
    change _ ∈ (⊥ : Submodule S (Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0)) at h2
    rw [Submodule.mem_bot, map_sub] at h2
    exact sub_eq_zero.mp h2
  have hj1 := congrFun heq ⟨⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩,
    Finset.card_singleton j⟩
  have hvj : v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ = w j := by
    rw [hv _ j (Finset.mem_singleton_self j), locRes_self]
  obtain ⟨g, s, e, hs, hse, hg, hgz, hwj⟩ := hwrep j hj
  obtain ⟨f, hf, hfm⟩ := mem_quotGraded_piece.mp m.2
  change LocalizedModule.mk (m : Poly S N ⧸ primeOf (S := S) y) 1 =
    v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ at hj1
  rw [hvj, hwj, ← hfm] at hj1
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hj1
  rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def] at hu
  change Ideal.Quotient.mk _ ((u : Poly S N) * (s * f)) = Ideal.Quotient.mk _ ((u : Poly S N) * g) at hu
  rw [Ideal.Quotient.eq, ← mul_sub] at hu
  have hu0 : (u : Poly S N) ∉ primeOf (S := S) y := by
    obtain ⟨eu, heu⟩ := monos_isHomogeneous u.2
    rw [mem_primeOf_of_isHomogeneous y heu]
    exact eval_ne_zero_of_mem_monos (singleChart hj) u.2
  have hsf := (Ideal.IsPrime.mem_or_mem inferInstance hu).resolve_left hu0
  have hfh : f.IsHomogeneous n := isHomogeneous_of_isWeightedHomogeneous_one hf
  have h1 : (s * f - g).IsHomogeneous (e + n) := (hse.mul hfh).sub hg
  rw [mem_primeOf_of_isHomogeneous y h1, map_sub, map_mul, hgz] at hsf
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have hzf : z = aeval y f := by
    have h3 : aeval y s * (aeval y f - z) = 0 := by linear_combination hsf
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hs0
    · exact (sub_eq_zero.mp h).symm
  rw [hzf]
  exact Submodule.subset_span ⟨f, n, hfh, rfl, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
