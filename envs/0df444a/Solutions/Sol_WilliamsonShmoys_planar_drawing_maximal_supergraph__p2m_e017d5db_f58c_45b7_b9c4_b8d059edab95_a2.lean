-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T10:24:10.450306+00:00
-- url     : https://prove2.me/submissions/f1c4496b-5711-45ac-939f-d4e8a8397f13

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        HasPlanarDrawingOn G →
          ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
            HasPlanarDrawingOn Q ∧
            (letI : DecidableRel G.Adj := dG
             letI : DecidableRel Q.Adj := dQ
             G.edgeFinset ⊆ Q.edgeFinset) ∧
            (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
              HasPlanarDrawingOn K →
                (letI : DecidableRel Q.Adj := dQ
                 letI : DecidableRel K.Adj := dK
                 Q.edgeFinset.card ≤ K.edgeFinset.card))) := by
  intro h
  let V := Fin 2
  let G : SimpleGraph V := ⊤
  letI dG : DecidableRel G.Adj := Classical.decRel _
  let p : V → ℝ × ℝ := fun x => ((x.val : ℝ), 0)
  let arc : V → V → ℝ → ℝ × ℝ :=
    fun u _ t => (if u = 0 then t else 1 - t, 0)
  have hp : Function.Injective p := by
    intro x y hxy
    apply Fin.ext
    have hv : (x.val : ℝ) = (y.val : ℝ) := congrArg Prod.fst hxy
    exact_mod_cast hv
  have hG : HasPlanarDrawingOn G := by
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hadj
      fin_cases u
      · fin_cases v
        · simp at huv
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simpa [arc] using continuousOn_id.prodMk continuousOn_const
          · intro t ht s hs hts
            have hf := congrArg Prod.fst hts
            simpa [arc] using hf
          · simp [arc, p]
          · simp [arc, p]
          · intro t ht w heq
            fin_cases w
            · have he : t = 0 := by
                simpa [arc, p] using congrArg Prod.fst heq
              linarith [ht.1]
            · have he : t = 1 := by
                simpa [arc, p] using congrArg Prod.fst heq
              linarith [ht.2]
      · fin_cases v <;> simp at huv
    · intro u v x y huv hxy hadj hadj' hneq t ht s hs heq
      fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;>
        simp [G] at *
  obtain ⟨Q, dQ, hQ, hrest⟩ :=
    @h V inferInstance inferInstance G dG hG
  rcases hrest with ⟨hsub, hmin⟩
  letI dQinst : DecidableRel Q.Adj := dQ
  let K : SimpleGraph V := ⊥
  letI dK : DecidableRel K.Adj := Classical.decRel _
  have hK : HasPlanarDrawingOn K := by
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hadj
      simp [K] at hadj
    · intro u v x y huv hxy hadj hadj' hneq t ht s hs heq
      simp [K] at hadj
  have hsubcard : G.edgeFinset.card ≤ Q.edgeFinset.card :=
    Finset.card_le_card hsub
  have hGcard : 1 ≤ G.edgeFinset.card := by
    simp [G]
  have hminZero : Q.edgeFinset.card ≤ 0 := by
    simpa [K, SimpleGraph.edgeFinset] using hmin K dK hK
  have hpositive : 1 ≤ Q.edgeFinset.card := le_trans hGcard hsubcard
  omega
