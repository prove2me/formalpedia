-- Prove2me | solution 1 for OPG37364.smallCut_expansion_of_spectralGap_gt_one_seventh
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T09:58:08.786278+00:00
-- url     : https://prove2.me/submissions/126b81a9-efa6-4cce-9313-e28b61a50aeb

import Definitions.Def_opg37364_cut_pairs
import Theorems.Thm_MarkovMixing_cheeger_upper
import Theorems.Thm_MarkovMixing_graph_walk_reversible

set_option autoImplicit false

open scoped BigOperators Classical

namespace OPG37364.Stage2Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma degree_fourteen (G : SimpleGraph V) (hreg : OPG37364.IsRegularOfDegree G 14)
    (v : V) : G.degree v = 14 := by
  have h := hreg v
  rw [Set.encard_eq_coe_toFinset_card] at h
  exact_mod_cast h

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : MarkovMixing.IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma walk_irreducible (G : SimpleGraph V) (hconn : OPG37364.IsConnected G)
    (hdeg : ∀ v, G.degree v = 14) (hP : MarkovMixing.IsStochastic (MarkovMixing.graphWalk G)) :
    MarkovMixing.Irreducible (MarkovMixing.graphWalk G) := by
  intro x y
  have hpath := hconn.2 x y
  induction hpath with
  | refl => exact ⟨0, by simp⟩
  | @tail b c hpath hbc ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 1, ?_⟩
    rw [pow_succ, Matrix.mul_apply]
    have hstep : 0 < MarkovMixing.graphWalk G b c := by
      simp [MarkovMixing.graphWalk, hbc, hdeg b]
    exact lt_of_lt_of_le (mul_pos ht hstep)
      (Finset.single_le_sum (fun z _ =>
        mul_nonneg (pow_entry_nonneg hP t x z) (hP.1 z c)) (Finset.mem_univ b))

lemma regular_walk_uniform [Nonempty V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v = 14) :
    MarkovMixing.IsStochastic (MarkovMixing.graphWalk G) ∧
    MarkovMixing.DetailedBalance (MarkovMixing.graphWalk G) (MarkovMixing.uniformDist V) ∧
    MarkovMixing.IsStationary (MarkovMixing.graphWalk G) (MarkovMixing.uniformDist V) := by
  obtain ⟨hP, hrev, hstat⟩ := MarkovMixing.graph_walk_reversible G
    (fun v => by rw [hdeg v]; norm_num)
  have htotal : (14 : ℝ) * Fintype.card V = 2 * (G.edgeFinset.card : ℝ) := by
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    exact_mod_cast (by simpa [Nat.mul_comm] using h : 14 * Fintype.card V = 2 * G.edgeFinset.card)
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card V ≠ 0)
  have heq : (fun v => (G.degree v : ℝ) / (2 * G.edgeFinset.card)) =
      MarkovMixing.uniformDist V := by
    funext v
    simp only [hdeg, MarkovMixing.uniformDist]
    rw [← htotal]
    field_simp
    norm_num
  rw [heq] at hrev hstat
  exact ⟨hP, hrev, hstat⟩

lemma cutPairs_toFinset (G : SimpleGraph V) (s : Finset V) :
    (OPG37364.cutPairs G (s : Set V)).toFinset =
      (s.product sᶜ).filter (fun e => G.Adj e.1 e.2) := by
  apply Finset.ext
  intro e
  rw [Set.mem_toFinset, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_compl.mpr hy⟩, hxy⟩
  · rintro ⟨he, hxy⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp he
    exact ⟨hx, Finset.mem_compl.mp hy, hxy⟩

lemma uniform_mass (s : Finset V) :
    (∑ x ∈ s, MarkovMixing.uniformDist V x) = (s.card : ℝ) / Fintype.card V := by
  simp [MarkovMixing.uniformDist, div_eq_mul_inv]

lemma crossing_flow (G : SimpleGraph V) (hdeg : ∀ v, G.degree v = 14) (s : Finset V) :
    (∑ x ∈ s, ∑ y ∈ sᶜ,
      MarkovMixing.edgeMeasure (MarkovMixing.graphWalk G) (MarkovMixing.uniformDist V) x y) =
    (((s.product sᶜ).filter (fun e => G.Adj e.1 e.2)).card : ℝ) *
      ((Fintype.card V : ℝ)⁻¹ * (14 : ℝ)⁻¹) := by
  rw [← Finset.sum_product']
  simp only [MarkovMixing.edgeMeasure, MarkovMixing.uniformDist, MarkovMixing.graphWalk,
    hdeg, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp

lemma ratio_nonneg (P : Matrix V V ℝ) (π : V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hπ : ∀ x, 0 ≤ π x) (s : Finset V) :
    0 ≤ MarkovMixing.bottleneckRatio P π s := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hπ x) (hP x y)
  · exact Finset.sum_nonneg fun x _ => hπ x

end OPG37364.Stage2Internal

open OPG37364 OPG37364.Stage2Internal

/-- An ordinary random-walk gap above 1/7 forces strict expansion of every small shore. -/
theorem solution
    {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hconn : IsConnected G) (hreg : IsRegularOfDegree G 14)
    (hgap : (1 : ℝ) / 7 < MarkovMixing.spectralGap (MarkovMixing.graphWalk G)) :
    ∀ S : Set (Fin n), S.Nonempty → Sᶜ.Nonempty →
      S.encard ≤ Sᶜ.encard → S.encard < (cutPairs G S).encard := by
  letI : Nonempty (Fin n) := hconn.1
  have hdeg := degree_fourteen G hreg
  obtain ⟨hP, hrev, hπ⟩ := regular_walk_uniform G hdeg
  have hirr := walk_irreducible G hconn hdeg hP
  have hcheeger := MarkovMixing.cheeger_upper (by simpa using hn)
    (MarkovMixing.graphWalk G) hP hirr (MarkovMixing.uniformDist (Fin n)) hπ hrev
  intro S hS hSc hsmall
  by_contra hnot
  have hle : (cutPairs G S).encard ≤ S.encard := le_of_not_gt hnot
  let s : Finset (Fin n) := S.toFinset
  let c : Finset (Fin n × Fin n) := (s.product sᶜ).filter (fun e => G.Adj e.1 e.2)
  have hs : (s : Set (Fin n)) = S := by simp [s]
  have hsne : s.Nonempty := by simpa [s] using hS
  have hk : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcard : s.card ≤ sᶜ.card := by
    rw [Set.encard_eq_coe_toFinset_card, Set.encard_eq_coe_toFinset_card,
      Set.toFinset_compl] at hsmall
    exact_mod_cast hsmall
  have htwok : (2 : ℝ) * s.card ≤ n := by
    have hsum := Finset.card_add_card_compl s
    simp only [Fintype.card_fin] at hsum
    have : 2 * s.card ≤ n := by omega
    exact_mod_cast this
  have hmass : (∑ x ∈ s, MarkovMixing.uniformDist (Fin n) x) = (s.card : ℝ) / n := by
    simpa using uniform_mass s
  have hhalf : (∑ x ∈ s, MarkovMixing.uniformDist (Fin n) x) ≤ (2 : ℝ)⁻¹ := by
    rw [hmass, div_le_iff₀ hnpos]
    linarith
  have hcut : (cutPairs G S).encard = (c.card : ℕ∞) := by
    rw [← hs, Set.encard_eq_coe_toFinset_card, cutPairs_toFinset]
  have hm : (c.card : ℝ) ≤ s.card := by
    rw [hcut, Set.encard_eq_coe_toFinset_card] at hle
    exact_mod_cast hle
  have hratio : MarkovMixing.bottleneckRatio (MarkovMixing.graphWalk G)
      (MarkovMixing.uniformDist (Fin n)) s = (c.card : ℝ) / (14 * s.card) := by
    unfold MarkovMixing.bottleneckRatio
    rw [crossing_flow G hdeg s, hmass]
    simp only [Fintype.card_fin]
    change (c.card : ℝ) * ((n : ℝ)⁻¹ * 14⁻¹) / ((s.card : ℝ) / n) = _
    field_simp
  have hrle : MarkovMixing.bottleneckRatio (MarkovMixing.graphWalk G)
      (MarkovMixing.uniformDist (Fin n)) s ≤ (1 : ℝ) / 14 := by
    rw [hratio, div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 14) hk)]
    linarith
  have hbdd : BddBelow (Set.range (fun a : {s : Finset (Fin n) // s.Nonempty ∧
      ∑ x ∈ s, MarkovMixing.uniformDist (Fin n) x ≤ (2 : ℝ)⁻¹} =>
      MarkovMixing.bottleneckRatio (MarkovMixing.graphWalk G) (MarkovMixing.uniformDist (Fin n)) a.1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact ratio_nonneg _ _ hP.1 hπ.1.1 a.1
  have hstar : MarkovMixing.bottleneckStar (MarkovMixing.graphWalk G)
      (MarkovMixing.uniformDist (Fin n)) ≤ (1 : ℝ) / 14 := by
    exact ciInf_le_of_le hbdd ⟨s, hsne, hhalf⟩ hrle
  linarith

