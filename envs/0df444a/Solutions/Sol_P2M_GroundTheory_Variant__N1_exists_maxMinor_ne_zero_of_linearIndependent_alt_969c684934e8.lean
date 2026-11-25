-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_exists_maxMinor_ne_zero_of_linearIndependent_alt_969c684934e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:54.226666+00:00
-- url     : https://prove2.me/submissions/6817787b-27d2-450e-9073-6db206dfc4d4

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
namespace GroundTheory.Variant₂.N1
theorem _root_.solution {R : Type*} [CommRing R] {n k : ℕ}
    [IsDomain R] (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 := by
  classical
  set K := FractionRing R
  set B' : Matrix (Fin n) (Fin k) K := B.map (algebraMap R K) with hB'
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h1 : LinearIndependent R B'.col := by
    have hker : LinearMap.ker ((Algebra.linearMap R K).compLeft (Fin n)) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      funext i
      exact hinj (congr_fun hxy i)
    have := hB.map' ((Algebra.linearMap R K).compLeft (Fin n)) hker
    have heq : B'.col = ((Algebra.linearMap R K).compLeft (Fin n)) ∘ B.col := by
      funext j i
      rfl
    rw [heq]
    exact this
  have h2 : LinearIndependent K B'.col := (LinearIndependent.iff_fractionRing R K).mp h1
  have hrank : B'.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h2, Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_row] at hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K B'.row
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← hrank, ← hspan, finrank_span_eq_card hli]
  let t : Finset (Fin n) := Finset.univ.map ⟨a, ha⟩
  have ht : t.card = k := by simp [t, hcard]
  let s : KSubset n k := ⟨t, ht⟩
  refine ⟨s, ?_⟩
  have hmem : ∀ i : Fin k, ∃ c : κ, a c = s.emb i := by
    intro i
    have h : s.emb i ∈ t := Finset.orderEmbOfFin_mem t ht i
    simp only [t, Finset.mem_map, Finset.mem_univ, true_and] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc⟩
  choose e he using hmem
  have he_inj : Function.Injective e := by
    intro i j hij
    apply s.emb.injective
    rw [← he i, ← he j, hij]
  have hrows : LinearIndependent K (B'.submatrix s.emb id).row := by
    have hfam : (B'.submatrix s.emb id).row = (B'.row ∘ a) ∘ e := by
      funext i j
      show B' (s.emb i) j = B' (a (e i)) j
      rw [he i]
    rw [hfam]
    exact hli.comp e he_inj
  have hdet : (B'.submatrix s.emb id).det ≠ 0 := by
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  intro h
  apply hdet
  have hmap : B'.submatrix s.emb id = (B.submatrix s.emb id).map (algebraMap R K) := rfl
  rw [hmap]
  show ((algebraMap R K).mapMatrix (B.submatrix s.emb id)).det = 0
  rw [← RingHom.map_det]
  unfold maxMinor at h
  rw [h, map_zero]
end GroundTheory.Variant₂.N1
