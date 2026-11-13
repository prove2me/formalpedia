-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_small_disc
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:05:43.060049+00:00
-- url     : https://prove2.me/submissions/08e91c4b-f164-465b-b90c-25bb337f651f

import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_1_1
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
set_option autoImplicit false
open scoped Classical BigOperators
open LocalLemmaHierarchy.Completeness ZeroFreeRRG.Hardcore

/-- An elementary uniform zero-free disc for bounded-degree independence polynomials. -/
theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hd : 1 ≤ d) (hG : ∀ v, G.degree v ≤ d) (z : ℂ)
    (hz : ‖z‖ ≤ (1 / ((d:ℝ)+1)) * (1 - 1 / ((d:ℝ)+1))^d) :
    hardcoreZfug G z ≠ 0 := by
  classical
  by_cases hv : IsEmpty V
  · letI : IsEmpty V := hv
    have hs (s : Finset V) : s = ∅ := Finset.eq_empty_of_forall_notMem (fun v _ => isEmptyElim v)
    simp [hardcoreZfug, Finset.univ_unique, hs]
  · letI : Nonempty V := not_isEmpty_iff.mp hv
    let o : NeighborOrders G := ⟨fun _ v => (Fintype.equivFin V v).val, by
      intro v x hx y hy hxy
      exact (Fintype.equivFin V).injective (Fin.ext hxy)⟩
    let c : ℝ := 1 / ((d:ℝ)+1)
    let p : ℝ := c * (1-c)^d
    have hden : (0:ℝ) < (d:ℝ)+1 := by positivity
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hc1 : c < 1 := by
      dsimp [c]
      apply (div_lt_one hden).2
      have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hbase0 : 0 ≤ 1-c := by linarith
    have hbase1 : 1-c ≤ 1 := by linarith
    have hp0 : 0 ≤ p := by dsimp [p]; positivity
    let x : Hist (indRep G o) → ℝ := fun _ => c
    have hcond : ∀ v, 0 ≤ x (indState G o v) ∧ x (indState G o v) < 1 ∧
        (fun _ : V => p) v ≤ x (indState G o v) *
          ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u)) := by
      intro v
      refine ⟨hc0,hc1,?_⟩
      have hcard : (G.neighborFinset v).card ≤ d := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hG v
      have hpow : (1-c)^d ≤ (1-c)^(G.neighborFinset v).card :=
        pow_le_pow_of_le_one hbase0 hbase1 hcard
      simpa [x,p] using mul_le_mul_of_nonneg_left hpow hc0
    have th := theorem_1_1 G o
    have hcert := ((th.2.1.1 (fun _ => p) (fun _ => hp0) x).2 hcond)
    have hzero := ((th.2.2.2.2 0 (fun _ => p) (fun _ => hp0) x hcert) Finset.univ).1
    have h := hzero (fun _ => z) (fun _ => by simpa [p,c] using hz)
    unfold hardcoreZfug
    simpa [indepPoly] using h
