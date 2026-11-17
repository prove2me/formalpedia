-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.safe_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:23:10.517914+00:00
-- url     : https://prove2.me/submissions/76ab5694-87ed-4c9e-a4d9-3a264917bd07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
import Definitions.Def_OfflineStochMatch_Attenuation_SideProb
import Theorems.Thm_OfflineStochMatch_Attenuation_safe_relaxed_integral
import Theorems.Thm_OfflineStochMatch_Attenuation_relaxed_bound

namespace OfflineStochMatch.Attenuation

section Aux

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem sb_coinWeight_nonneg {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (c : ι → Bool) : 0 ≤ coinWeight q c :=
  Finset.prod_nonneg fun i _ => by unfold bern; split_ifs <;> linarith [hq i]

theorem sb_step_probes_le (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (Y A P : E → Bool) (st : RunState V) (f : E) (r : V) :
    (step G t Y A P st f).probes r ≤ st.probes r +
      (if r ∈ G.ends f ∧ Y f = true ∧ A f = true then 1 else 0) := by
  unfold step
  by_cases h : CanProbe G t st f ∧ Y f = true ∧ A f = true
  · rw [if_pos h]
    by_cases hr : r ∈ G.ends f
    · simp [hr, h.2.1, h.2.2]
    · simp [hr]
  · rw [if_neg h]; omega

theorem sb_foldl_probes_le (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (Y A P : E → Bool) (r : V) (L : List E) (st : RunState V) :
    (L.foldl (step G t Y A P) st).probes r ≤ st.probes r +
      (L.filter (fun f => decide (r ∈ G.ends f ∧ Y f = true ∧ A f = true))).length := by
  induction L generalizing st with
  | nil => simp
  | cons f L ih =>
    simp only [List.foldl_cons]
    refine (ih _).trans ?_
    have hs := sb_step_probes_le G t Y A P st f r
    by_cases hc : r ∈ G.ends f ∧ Y f = true ∧ A f = true
    · rw [List.filter_cons_of_pos (by simpa using hc)]
      simp only [List.length_cons]
      rw [if_pos hc] at hs
      omega
    · rw [List.filter_cons_of_neg (by simpa using hc)]
      rw [if_neg hc] at hs
      omega

theorem sb_probes_le_card (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (r : V) :
    (stateBefore G t σ Y A P e).probes r ≤ ((otherIncident G e r).filter
        (fun f => arrivedBefore σ e f = true ∧ Y f = true ∧ A f = true)).card := by
  unfold stateBefore
  refine (sb_foldl_probes_le G t Y A P r _ initState).trans ?_
  have h0 : (initState : RunState V).probes r = 0 := rfl
  rw [h0, zero_add]
  have hnd : (((List.finRange (Fintype.card E)).filter
      (fun i => decide (i < σ e))).map σ.symm).Nodup :=
    ((List.nodup_finRange _).filter _).map σ.symm.injective
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  apply Finset.card_le_card
  intro f hf
  simp only [List.mem_toFinset, List.mem_filter, List.mem_map, List.mem_finRange, true_and,
    decide_eq_true_eq] at hf
  obtain ⟨⟨i, hi, rfl⟩, hr', hY, hA⟩ := hf
  have hne : σ.symm i ≠ e := by
    intro h
    rw [← h] at hi
    simp at hi
  simp only [otherIncident, incident, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
    true_and, arrivedBefore, decide_eq_true_eq, Equiv.apply_symm_apply]
  exact ⟨⟨hne, hr'⟩, hi, hY, hA⟩

theorem sb_safe_of_sideOK (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E) (u v : V)
    (huv : G.ends e = s(u, v))
    (hu : SideOK G t e u (arrivedBefore σ e) Y A P)
    (hv : SideOK G t e v (arrivedBefore σ e) Y A P) :
    IsSafe G t σ Y A P e := by
  have hall : ∀ r, r ∈ G.ends e → SideOK G t e r (arrivedBefore σ e) Y A P := by
    intro r hr
    rw [huv, Sym2.mem_iff] at hr
    rcases hr with rfl | rfl <;> assumption
  refine ⟨fun r hr => ?_, fun f hfe hex hlt => ?_⟩
  · have hS := (hall r hr).2
    have key := sb_probes_le_card G t σ Y A P e r
    calc ((stateBefore G t σ Y A P e).probes r : ℕ∞) + 1
        ≤ (((otherIncident G e r).filter
            (fun f => arrivedBefore σ e f = true ∧ Y f = true ∧ A f = true)).card : ℕ∞) + 1 := by
          have hk : ((stateBefore G t σ Y A P e).probes r : ℕ∞) ≤
              (((otherIncident G e r).filter
                (fun f => arrivedBefore σ e f = true ∧ Y f = true ∧ A f = true)).card : ℕ∞) := by
            exact_mod_cast key
          exact add_le_add hk le_rfl
      _ ≤ t r := hS
  · obtain ⟨r, hre, hrf⟩ := hex
    have h1 := (hall r hre).1 f (by simp [otherIncident, incident, hfe, hrf])
    rintro ⟨hA, hP, hY⟩
    exact h1 ⟨by simp [arrivedBefore, hlt], hY, hA, hP⟩

theorem sb_prob_mono (p y a : E → ℝ) (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1)
    (hy : ∀ f, 0 ≤ y f ∧ y f ≤ 1) (ha : ∀ f, 0 ≤ a f ∧ a f ≤ 1)
    (ev1 ev2 : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop)
    (himp : ∀ σ Y A P, ev1 σ Y A P → ev2 σ Y A P) :
    prob p y a ev1 ≤ prob p y a ev2 := by
  unfold prob
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum; intro σ _
  apply Finset.sum_le_sum; intro Y _
  apply Finset.sum_le_sum; intro A _
  apply Finset.sum_le_sum; intro P _
  have hw : 0 ≤ coinWeight y Y * coinWeight a A * coinWeight p P :=
    mul_nonneg (mul_nonneg (sb_coinWeight_nonneg y hy Y) (sb_coinWeight_nonneg a ha A))
      (sb_coinWeight_nonneg p hp P)
  apply mul_le_mul_of_nonneg_left _ hw
  by_cases h1 : ev1 σ Y A P
  · rw [if_pos h1, if_pos (himp σ Y A P h1)]
  · rw [if_neg h1]
    split_ifs <;> norm_num

end Aux

theorem sb_att_range (aT : ℝ → ℝ) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ aT z ∧ aT z ≤ 1 := by
  intro z hz
  rcases haT with rfl | rfl
  · simp only [expAtt]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith [hz.1])⟩
  · simp only [linAtt]
    constructor <;> linarith [hz.1, hz.2]

theorem safe_bound_main {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, 2 ≤ t v) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) :
    betaStar ≤ aT (p e * y e) * probSafe G p t y aT e := by
  have hrep : ∀ z : Sym2 V, ∃ a b, z = s(a, b) := fun z => Sym2.ind (fun a b => ⟨a, b, rfl⟩) z
  obtain ⟨u, v, huv⟩ := hrep (G.ends e)
  have hyb : ∀ f, 0 ≤ y f ∧ y f ≤ 1 := hy.1
  have haR := sb_att_range aT haT
  have hpy : ∀ f, p f * y f ∈ Set.Icc (0 : ℝ) 1 := fun f =>
    ⟨mul_nonneg (hp f).1 (hyb f).1, by nlinarith [(hp f).1, (hp f).2, (hyb f).1, (hyb f).2]⟩
  have hatt : ∀ f, 0 ≤ attProb aT p y f ∧ attProb aT p y f ≤ 1 := fun f => haR _ (hpy f)
  have hmono : prob p y (attProb aT p y) (fun σ Y A P =>
      SideOK G t e u (arrivedBefore σ e) Y A P ∧ SideOK G t e v (arrivedBefore σ e) Y A P) ≤
      probSafe G p t y aT e :=
    sb_prob_mono p y (attProb aT p y) hp hyb hatt _ _
      (fun σ Y A P h => sb_safe_of_sideOK G t σ Y A P e u v huv h.1 h.2)
  have h1 := relaxed_bound G hG p y t aT hp ht hy haT e u v huv
  have h2 := safe_relaxed_integral G hG p y t aT e u v huv
  have haE : 0 ≤ aT (p e * y e) := (haR _ (hpy e)).1
  rw [← h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hmono haE)

end OfflineStochMatch.Attenuation

open OfflineStochMatch.Attenuation

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, 2 ≤ t v) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) :
    betaStar ≤ aT (p e * y e) * probSafe G p t y aT e :=
  safe_bound_main G hG p y t aT hp ht hy haT e
