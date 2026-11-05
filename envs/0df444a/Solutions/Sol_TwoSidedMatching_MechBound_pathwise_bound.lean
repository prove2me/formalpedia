-- Prove2me | solution 1 for TwoSidedMatching.MechBound.pathwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:05:34.512157+00:00
-- url     : https://prove2.me/submissions/309517a2-259a-47f3-95be-0e142346d139

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.MechBound.PathwiseAux

lemma sum_fin_get {X : Type*} (L : List X) (g : X → ℝ) :
    ∑ i : Fin L.length, g (L.get i) = (L.map g).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

lemma map_ite_sum {X : Type*} (L : List X) (p : X → Prop) [DecidablePred p] :
    ((L.map (fun x => if p x then (1:ℝ) else 0)).sum) = ((L.filter p).length : ℝ) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a
    · simp [ha, List.filter_cons, ih]; ring
    · simp [ha, List.filter_cons, ih]

lemma card_idx {X : Type*} (L : List X) (p : X → Prop) [DecidablePred p] :
    Fintype.card {i : Fin L.length // p (L.get i)} = (L.filter p).length := by
  rw [Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ i : Fin L.length, (if p (L.get i) then (1:ℝ) else 0)) =
      (L.map (fun x => if p x then (1:ℝ) else 0)).sum :=
    sum_fin_get L (fun x => if p x then (1:ℝ) else 0)
  have h2 := map_ite_sum L p
  have h3 : ((∑ i : Fin L.length, (if p (L.get i) then 1 else 0) : ℕ) : ℝ) =
      ∑ i : Fin L.length, (if p (L.get i) then (1:ℝ) else 0) := by
    push_cast; rfl
  exact_mod_cast h3.trans (h1.trans h2)

end TwoSidedMatching.MechBound.PathwiseAux

open TwoSidedMatching.MechBound TwoSidedMatching.MechBound.PathwiseAux

theorem solution
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (D S : Multiset (ℝ × ℝ)) (oD oS : ℝ × ℝ → Outcome)
    (hD : ∀ φ ∈ D, φ ∈ buyerTypes E T) (hS : ∀ ψ ∈ S, ψ ∈ sellerTypes E T)
    (hoD : ∀ φ ∈ D, AgentFeasible T φ (oD φ)) (hoS : ∀ ψ ∈ S, AgentFeasible T ψ (oS ψ))
    (hbal : Balanced T D S oD oS) :
    (D.map (fun φ => E.psiB φ.2 * (oD φ).m - b * ((oD φ).s - φ.1))).sum -
        (S.map (fun ψ => E.psiS ψ.2 * (oS ψ).m + h * ((oS ψ).s - ψ.1))).sum ≤
      JbarProfile E b h D S := by
  classical
  set LD := D.toList with hLD
  set LS := S.toList with hLS
  have hDL : (LD : Multiset (ℝ × ℝ)) = D := Multiset.coe_toList D
  have hSL : (LS : Multiset (ℝ × ℝ)) = S := Multiset.coe_toList S
  have memD : ∀ i : Fin LD.length, LD.get i ∈ D := fun i => by
    rw [← hDL]; exact Multiset.mem_coe.2 (List.get_mem _ _)
  have memS : ∀ j : Fin LS.length, LS.get j ∈ S := fun j => by
    rw [← hSL]; exact Multiset.mem_coe.2 (List.get_mem _ _)
  -- rewrite the multiset sums as sums over indices
  set F : ℝ × ℝ → ℝ := fun φ => E.psiB φ.2 * (oD φ).m - b * ((oD φ).s - φ.1) with hF
  set G : ℝ × ℝ → ℝ := fun ψ => E.psiS ψ.2 * (oS ψ).m + h * ((oS ψ).s - ψ.1) with hG
  have eD : (D.map F).sum = ∑ i : Fin LD.length, F (LD.get i) := by
    rw [sum_fin_get, ← Multiset.sum_coe, ← Multiset.map_coe, hDL]
  have eS : (S.map G).sum = ∑ j : Fin LS.length, G (LS.get j) := by
    rw [sum_fin_get, ← Multiset.sum_coe, ← Multiset.map_coe, hSL]
  rw [eD, eS]
  -- matched agents
  let α := {i : Fin LD.length // (oD (LD.get i)).m = 1}
  let β := {j : Fin LS.length // (oS (LS.get j)).m = 1}
  let f : α → ℝ := fun a => (oD (LD.get a.1)).s
  let g : β → ℝ := fun c => (oS (LS.get c.1)).s
  have hcard : ∀ c : ℝ, Fintype.card {a : α // f a = c} = Fintype.card {x : β // g x = c} := by
    intro c
    have e1 : Fintype.card {a : α // f a = c} =
        Fintype.card {i : Fin LD.length // (fun φ => (oD φ).s = c ∧ (oD φ).m = 1) (LD.get i)} := by
      apply Fintype.card_congr
      exact { toFun := fun a => ⟨a.1.1, a.2, a.1.2⟩
              invFun := fun i => ⟨⟨i.1, i.2.2⟩, i.2.1⟩
              left_inv := fun a => rfl
              right_inv := fun i => rfl }
    have e2 : Fintype.card {x : β // g x = c} =
        Fintype.card {j : Fin LS.length // (fun ψ => (oS ψ).s = c ∧ (oS ψ).m = 1) (LS.get j)} := by
      apply Fintype.card_congr
      exact { toFun := fun a => ⟨a.1.1, a.2, a.1.2⟩
              invFun := fun i => ⟨⟨i.1, i.2.2⟩, i.2.1⟩
              left_inv := fun a => rfl
              right_inv := fun i => rfl }
    rw [e1, e2]
    refine (card_idx LD (fun φ => (oD φ).s = c ∧ (oD φ).m = 1)).trans
      (Eq.trans ?_ (card_idx LS (fun ψ => (oS ψ).s = c ∧ (oS ψ).m = 1)).symm)
    by_cases hc : c ∈ Set.Icc 0 T
    · have := hbal c hc
      rw [← hDL, ← hSL] at this
      simpa [Multiset.filter_coe] using this
    · have z1 : (LD.filter (fun φ => (oD φ).s = c ∧ (oD φ).m = 1)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro φ hφ
        have hφD : φ ∈ D := by rw [← hDL]; exact Multiset.mem_coe.2 hφ
        obtain ⟨h1, h2, -⟩ := hoD φ hφD
        have h0 := (hD φ hφD).1.1
        intro hh'
        apply hc
        simp only [decide_eq_true_eq] at hh'
        rw [← hh'.1]
        exact ⟨h0.trans h1, h2⟩
      have z2 : (LS.filter (fun ψ => (oS ψ).s = c ∧ (oS ψ).m = 1)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro ψ hψ
        have hψS : ψ ∈ S := by rw [← hSL]; exact Multiset.mem_coe.2 hψ
        obtain ⟨h1, h2, -⟩ := hoS ψ hψS
        have h0 := (hS ψ hψS).1.1
        intro hh'
        apply hc
        simp only [decide_eq_true_eq] at hh'
        rw [← hh'.1]
        exact ⟨h0.trans h1, h2⟩
      rw [z1, z2]
  let e : α ≃ β := Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c))
  have he : ∀ a, g (e a) = f a := fun a => Equiv.ofFiberEquiv_map _ a
  -- the matching
  let Pm : Finset (Fin LS.length × Fin LD.length) :=
    (Finset.univ : Finset α).image (fun a => ((e a).1, a.1))
  have hinj : Function.Injective (fun a : α => ((e a).1, a.1)) := by
    intro a a' haa
    exact Subtype.ext (congrArg Prod.snd haa)
  have hPm : Pm ∈ AssignmentGame.CoreLP.matchings Finset.univ Finset.univ := by
    unfold AssignmentGame.CoreLP.matchings
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.2 (by intro p _; simp), by intro p _; simp, ?_, ?_⟩
    · intro p hp q hq hpq
      simp only [Pm, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨a, rfl⟩ := hp
      obtain ⟨a', rfl⟩ := hq
      have : e a = e a' := Subtype.ext hpq
      rw [e.injective this]
    · intro p hp q hq hpq
      simp only [Pm, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨a, rfl⟩ := hp
      obtain ⟨a', rfl⟩ := hq
      have : a = a' := Subtype.ext hpq
      rw [this]
  have hworth : (∑ a : α, weight E b h (LD.get a.1) (LS.get (e a).1)) ≤ JbarProfile E b h D S := by
    unfold JbarProfile
    have := Finset.le_sup' (fun P => ∑ p ∈ P, weight E b h (D.toList.get p.2) (S.toList.get p.1)) hPm
    refine le_trans (le_of_eq ?_) this
    simp only [Pm]
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
  -- buyer side
  have hDle : ∑ i : Fin LD.length, F (LD.get i) ≤ ∑ a : α, F (LD.get a.1) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin LD.length => (oD (LD.get i)).m = 1))
      (fun i => by simp) (fun i => F (LD.get i))]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin LD.length => (oD (LD.get i)).m = 1)]
    have : ∑ i ∈ Finset.univ.filter (fun i : Fin LD.length => ¬ (oD (LD.get i)).m = 1),
        F (LD.get i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨h1, -, hm⟩ := hoD _ (memD i)
      have hm0 : (oD (LD.get i)).m = 0 := hm.resolve_right hi
      simp only [hF, hm0, mul_zero, zero_sub, neg_nonpos]
      exact mul_nonneg hb (by linarith)
    linarith
  have hSge : ∑ c : β, G (LS.get c.1) ≤ ∑ j : Fin LS.length, G (LS.get j) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun j : Fin LS.length => (oS (LS.get j)).m = 1))
      (fun j => by simp) (fun j => G (LS.get j))]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨h1, -, hm⟩ := hoS _ (memS j)
    have hm0 : (oS (LS.get j)).m = 0 := hm.resolve_right hj
    simp only [hG, hm0, mul_zero, zero_add]
    exact mul_nonneg hh (by linarith)
  have hreidx : ∑ c : β, G (LS.get c.1) = ∑ a : α, G (LS.get (e a).1) :=
    (Equiv.sum_comp e (fun c => G (LS.get c.1))).symm
  have hterm : ∀ a : α, F (LD.get a.1) - G (LS.get (e a).1) ≤
      weight E b h (LD.get a.1) (LS.get (e a).1) := by
    intro a
    have hma : (oD (LD.get a.1)).m = 1 := a.2
    have hmb : (oS (LS.get (e a).1)).m = 1 := (e a).2
    have hs : (oS (LS.get (e a).1)).s = (oD (LD.get a.1)).s := he a
    obtain ⟨hD1, -, -⟩ := hoD _ (memD a.1)
    obtain ⟨hS1, -, -⟩ := hoS _ (memS (e a).1)
    set s := (oD (LD.get a.1)).s
    set tφ := (LD.get a.1).1
    set tψ := (LS.get (e a).1).1
    simp only [hF, hG, weight, hma, hmb, hs, mul_one]
    rw [hs] at hS1
    have k1 : b * max (tψ - tφ) 0 ≤ b * (s - tφ) :=
      mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hb
    have k2 : h * max (tφ - tψ) 0 ≤ h * (s - tψ) :=
      mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hh
    linarith
  calc ∑ i : Fin LD.length, F (LD.get i) - ∑ j : Fin LS.length, G (LS.get j)
      ≤ ∑ a : α, F (LD.get a.1) - ∑ a : α, G (LS.get (e a).1) := by
        rw [← hreidx]; linarith
    _ = ∑ a : α, (F (LD.get a.1) - G (LS.get (e a).1)) := (Finset.sum_sub_distrib _ _).symm
    _ ≤ ∑ a : α, weight E b h (LD.get a.1) (LS.get (e a).1) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ ≤ JbarProfile E b h D S := hworth
