-- Prove2me | solution 1 for SWSSNet.Diffusion.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:06:49.519199+00:00
-- url     : https://prove2.me/submissions/aeb24df5-5474-4e5b-bd54-5b1f081bdf2b

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network
import Theorems.Thm_SWSSNet_Diffusion_atar_prop_A_2
import Theorems.Thm_SWSSNet_Diffusion_proposition_2

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSGainAux

open SWSSNet.Diffusion

variable {I J : ℕ}

theorem bip_adj_iff (adj : Fin I → Fin J → Prop) (a b : Fin I ⊕ Fin J) :
    (bipGraph adj).Adj a b ↔
      (∃ i j, a = Sum.inl i ∧ b = Sum.inr j ∧ adj i j) ∨
      (∃ i j, b = Sum.inl i ∧ a = Sum.inr j ∧ adj i j) := by
  unfold bipGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨i, j, rfl, rfl, _⟩ | ⟨i, j, rfl, rfl, _⟩ <;> simp

/-- `flowMap` is the unique flow on `D`. -/
theorem flowMap_eq (N : TreeNetwork I J) {α : Fin I → ℝ} {β : Fin J → ℝ} (hD : ∑ i, α i = ∑ j, β j)
    {z : Fin I → Fin J → ℝ} (hz : IsFlow N α β z) : flowMap N α β = z := by
  classical
  have h := atar_prop_A_2 N α β hD
  unfold flowMap
  rw [dif_pos h]
  exact h.unique h.exists.choose_spec hz

theorem flowMap_isFlow (N : TreeNetwork I J) {α : Fin I → ℝ} {β : Fin J → ℝ}
    (hD : ∑ i, α i = ∑ j, β j) : IsFlow N α β (flowMap N α β) := by
  obtain ⟨z, hz, -⟩ := atar_prop_A_2 N α β hD
  rw [flowMap_eq N hD hz]; exact hz

/-- Elementary flow along one step of a walk. -/
def ed (x y : Fin I ⊕ Fin J) (i : Fin I) (j : Fin J) : ℝ :=
  (if x = Sum.inl i ∧ y = Sum.inr j then 1 else 0) - (if x = Sum.inr j ∧ y = Sum.inl i then 1 else 0)

/-- The flow carried by a walk. -/
def pfw (adj : Fin I → Fin J → Prop) :
    {a b : Fin I ⊕ Fin J} → (bipGraph adj).Walk a b → Fin I → Fin J → ℝ
  | _, _, .nil => 0
  | a, _, .cons (v := c) _ p => ed a c + pfw adj p

theorem ed_supp (adj : Fin I → Fin J → Prop) {x y : Fin I ⊕ Fin J} (h : (bipGraph adj).Adj x y)
    (i : Fin I) (j : Fin J) (hn : ¬ adj i j) : ed x y i j = 0 := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i', j', rfl, rfl, h⟩ | ⟨i', j', rfl, rfl, h⟩
  · unfold ed
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij; exact absurd h hn
    · simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, if_false, sub_zero]
      rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hij ⟨rfl, rfl⟩
  · unfold ed
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij; exact absurd h hn
    · simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, if_false, zero_sub,
        neg_eq_zero]
      rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hij ⟨rfl, rfl⟩

theorem ed_row (adj : Fin I → Fin J → Prop) {x y : Fin I ⊕ Fin J} (h : (bipGraph adj).Adj x y)
    (i : Fin I) :
    ∑ j, ed x y i j = (if x = Sum.inl i then 1 else 0) - (if y = Sum.inl i then 1 else 0) := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i', j', rfl, rfl, _⟩ | ⟨i', j', rfl, rfl, _⟩
  · by_cases hi : i' = i
    · subst hi; simp [ed]
    · simp [ed, hi]
  · by_cases hi : i' = i
    · subst hi; simp [ed]
    · simp [ed, hi]

theorem ed_col (adj : Fin I → Fin J → Prop) {x y : Fin I ⊕ Fin J} (h : (bipGraph adj).Adj x y)
    (j : Fin J) :
    ∑ i, ed x y i j = (if y = Sum.inr j then 1 else 0) - (if x = Sum.inr j then 1 else 0) := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i', j', rfl, rfl, _⟩ | ⟨i', j', rfl, rfl, _⟩
  · by_cases hj : j' = j
    · subst hj; simp [ed]
    · simp [ed, hj]
  · by_cases hj : j' = j
    · subst hj; simp [ed]
    · simp [ed, hj]

theorem pfw_supp (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J} (w : (bipGraph adj).Walk a b)
    (i : Fin I) (j : Fin J) (hn : ¬ adj i j) : pfw adj w i j = 0 := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    simp only [pfw, Pi.add_apply, ih, add_zero]
    exact ed_supp adj h i j hn

theorem pfw_row (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J} (w : (bipGraph adj).Walk a b)
    (i : Fin I) :
    ∑ j, pfw adj w i j = (if a = Sum.inl i then 1 else 0) - (if b = Sum.inl i then 1 else 0) := by
  induction w with
  | nil => simp [pfw]
  | cons h p ih =>
    simp only [pfw, Pi.add_apply, Finset.sum_add_distrib, ih, ed_row adj h]
    ring

theorem pfw_col (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J} (w : (bipGraph adj).Walk a b)
    (j : Fin J) :
    ∑ i, pfw adj w i j = (if b = Sum.inr j then 1 else 0) - (if a = Sum.inr j then 1 else 0) := by
  induction w with
  | nil => simp [pfw]
  | cons h p ih =>
    simp only [pfw, Pi.add_apply, Finset.sum_add_distrib, ih, ed_col adj h]
    ring

theorem pfw_not_mem (adj : Fin I → Fin J → Prop) {a b : Fin I ⊕ Fin J}
    (w : (bipGraph adj).Walk a b) (i : Fin I) (hi : Sum.inl i ∉ w.support) (j : Fin J) :
    pfw adj w i j = 0 := by
  induction w with
  | nil => rfl
  | @cons x c y h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hi
    simp only [pfw, Pi.add_apply, ih hi.2, add_zero]
    have hc : c ≠ Sum.inl i := fun hc => hi.2 (hc ▸ p.start_mem_support)
    unfold ed
    rw [if_neg (fun hh => hi.1 hh.1.symm), if_neg (fun hh => hc hh.2)]
    simp

/-- The flow of a walk from class `k` to pool `ĵ` solves (37) for `(e_k, e_ĵ)`. -/
theorem pfw_isFlow (N : TreeNetwork I J) (k : Fin I) (ĵ : Fin J)
    (w : (bipGraph N.adj).Walk (Sum.inl k) (Sum.inr ĵ)) :
    IsFlow N (Pi.single k 1) (Pi.single ĵ 1) (pfw N.adj w) := by
  refine ⟨fun i j hn => pfw_supp N.adj w i j hn, fun i => ?_, fun j => ?_⟩
  · rw [pfw_row]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [pfw_col]
    by_cases h : j = ĵ
    · subst h; simp
    · simp [h, Ne.symm h]

theorem flowMap_single (N : TreeNetwork I J) (k : Fin I) (ĵ : Fin J)
    (w : (bipGraph N.adj).Walk (Sum.inl k) (Sum.inr ĵ)) :
    flowMap N (Pi.single k 1) (Pi.single ĵ 1) = pfw N.adj w :=
  flowMap_eq N (by simp) (pfw_isFlow N k ĵ w)



/-- A pool forces a class: the CRP column sums equal `1`. -/
theorem exists_class (N : TreeNetwork I J) (ĵ : Fin J) : Nonempty (Fin I) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := N.xi_crp.2.2.2.1 ĵ
  simp at this

/-- Every pool has a neighbouring class in the tree. -/
theorem exists_neighbor (N : TreeNetwork I J) (ĵ : Fin J) : ∃ î, N.adj î ĵ := by
  obtain ⟨i0⟩ := exists_class N ĵ
  obtain ⟨w⟩ := N.isTree.isConnected.preconnected (Sum.inr ĵ) (Sum.inl i0)
  cases w with
  | cons h _ =>
    rw [bip_adj_iff] at h
    rcases h with ⟨i, j, h1, _, _⟩ | ⟨i, j, h1, h2, h3⟩
    · cases h1
    · cases h2
      exact ⟨i, h3⟩

theorem treePath_isPath (N : TreeNetwork I J) (a b : Fin I ⊕ Fin J) : (treePath N a b).IsPath :=
  (N.isTree.existsUnique_path a b).exists.choose_spec

theorem treePath_unique (N : TreeNetwork I J) {a b : Fin I ⊕ Fin J}
    (w : (bipGraph N.adj).Walk a b) (hw : w.IsPath) : w = treePath N a b :=
  (N.isTree.existsUnique_path a b).unique hw (treePath_isPath N a b)

/-- Product of step weights along a walk. -/
noncomputable def wprod (N : TreeNetwork I J) {a b : Fin I ⊕ Fin J} (w : (bipGraph N.adj).Walk a b) : ℝ :=
  (w.darts.map fun d => stepWeight N d.fst d.snd).prod

theorem wprod_cons (N : TreeNetwork I J) {a c b : Fin I ⊕ Fin J} (h : (bipGraph N.adj).Adj a c)
    (p : (bipGraph N.adj).Walk c b) :
    wprod N (SimpleGraph.Walk.cons h p) = stepWeight N a c * wprod N p := by
  simp [wprod]

theorem wprod_nil (N : TreeNetwork I J) (a : Fin I ⊕ Fin J) :
    wprod N (SimpleGraph.Walk.nil : (bipGraph N.adj).Walk a a) = 1 := by
  simp [wprod]

theorem gain_eq_wprod (N : TreeNetwork I J) {a b : Fin I ⊕ Fin J} (w : (bipGraph N.adj).Walk a b)
    (hw : w.IsPath) : gain N a b = wprod N w := by
  rw [treePath_unique N w hw]; rfl

theorem sw_pos (N : TreeNetwork I J) {x y : Fin I ⊕ Fin J} (h : (bipGraph N.adj).Adj x y) :
    0 < stepWeight N x y := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i, j, rfl, rfl, h⟩ | ⟨i, j, rfl, rfl, h⟩
  · exact N.mu_pos i j h
  · simp only [stepWeight]; exact one_div_pos.mpr (N.mu_pos i j h)

theorem sw_inv (N : TreeNetwork I J) {x y : Fin I ⊕ Fin J} (h : (bipGraph N.adj).Adj x y) :
    stepWeight N x y * stepWeight N y x = 1 := by
  rw [bip_adj_iff] at h
  rcases h with ⟨i, j, rfl, rfl, h⟩ | ⟨i, j, rfl, rfl, h⟩
  · simp only [stepWeight]; field_simp [(N.mu_pos i j h).ne']
  · simp only [stepWeight]; field_simp [(N.mu_pos i j h).ne']

theorem wprod_pos (N : TreeNetwork I J) {a b : Fin I ⊕ Fin J} (w : (bipGraph N.adj).Walk a b) :
    0 < wprod N w := by
  induction w with
  | nil => simp [wprod]
  | cons h p ih => rw [wprod_cons]; exact mul_pos (sw_pos N h) ih

/-- The potential `φ(v) = gain(v, ĵ)`. -/
noncomputable def phi (N : TreeNetwork I J) (ĵ : Fin J) (v : Fin I ⊕ Fin J) : ℝ := gain N v (Sum.inr ĵ)

theorem phi_pos (N : TreeNetwork I J) (ĵ : Fin J) (v : Fin I ⊕ Fin J) : 0 < phi N ĵ v :=
  wprod_pos N _

theorem phi_root (N : TreeNetwork I J) (ĵ : Fin J) : phi N ĵ (Sum.inr ĵ) = 1 := by
  unfold phi
  rw [gain_eq_wprod N SimpleGraph.Walk.nil (by simp), wprod_nil]

theorem local_aux (N : TreeNetwork I J) (ĵ : Fin J) {x y : Fin I ⊕ Fin J}
    (hxy : (bipGraph N.adj).Adj x y) (p : (bipGraph N.adj).Walk y (Sum.inr ĵ)) (hp : p.IsPath) :
    phi N ĵ x = stepWeight N x y * wprod N p := by
  by_cases hx : x ∈ p.support
  · have hsnd := N.isTree.isAcyclic.eq_snd_of_adj_start hp hxy.symm hx
    cases p with
    | nil => exact absurd (by simpa using hx) hxy.ne
    | @cons _ c _ h q =>
      simp only [SimpleGraph.Walk.snd_cons] at hsnd
      subst hsnd
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      rw [wprod_cons, ← gain_eq_wprod N q hp.1]
      unfold phi
      rw [← mul_assoc, sw_inv N hxy, one_mul]
  · unfold phi
    rw [gain_eq_wprod N (SimpleGraph.Walk.cons hxy p) (hp.cons hx), wprod_cons]

/-- Local relation `φ(x) = w(x,y) φ(y)` along every edge. -/
theorem phi_local (N : TreeNetwork I J) (ĵ : Fin J) {x y : Fin I ⊕ Fin J}
    (hxy : (bipGraph N.adj).Adj x y) : phi N ĵ x = stepWeight N x y * phi N ĵ y := by
  rw [local_aux N ĵ hxy (treePath N y (Sum.inr ĵ)) (treePath_isPath N _ _)]
  rfl

theorem wprod_ratio (N : TreeNetwork I J) (ĵ : Fin J) {a b : Fin I ⊕ Fin J}
    (w : (bipGraph N.adj).Walk a b) : wprod N w * phi N ĵ b = phi N ĵ a := by
  induction w with
  | nil => simp [wprod]
  | cons h p ih => rw [wprod_cons, mul_assoc, ih, ← phi_local N ĵ h]

theorem gain_ratio (N : TreeNetwork I J) (ĵ : Fin J) (a b : Fin I ⊕ Fin J) :
    gain N a b = phi N ĵ a / phi N ĵ b := by
  rw [eq_div_iff (phi_pos N ĵ b).ne']
  exact wprod_ratio N ĵ (treePath N a b)

/-- Edge identity: `µ_ij / φ(i) = 1 / φ(j)` on edges. -/
theorem mu_div_phi (N : TreeNetwork I J) (ĵ : Fin J) {i : Fin I} {j : Fin J} (h : N.adj i j) :
    N.mu i j / phi N ĵ (Sum.inl i) = 1 / phi N ĵ (Sum.inr j) := by
  have hadj : (bipGraph N.adj).Adj (Sum.inl i) (Sum.inr j) := by
    rw [bip_adj_iff]; exact Or.inl ⟨i, j, rfl, rfl, h⟩
  rw [phi_local N ĵ hadj]
  simp only [stepWeight]
  have := phi_pos N ĵ (Sum.inr j)
  have := N.mu_pos i j h
  field_simp

/-- The potential `Q`: `0` on classes, `1/φ` on pools. -/
noncomputable def Q (N : TreeNetwork I J) (ĵ : Fin J) : Fin I ⊕ Fin J → ℝ
  | Sum.inl _ => 0
  | Sum.inr j => 1 / phi N ĵ (Sum.inr j)

theorem ed_weighted (N : TreeNetwork I J) (ĵ : Fin J) {x y : Fin I ⊕ Fin J}
    (h : (bipGraph N.adj).Adj x y) :
    ∑ i, ∑ j, 1 / phi N ĵ (Sum.inl i) * (N.mu i j * ed x y i j) = Q N ĵ y - Q N ĵ x := by
  have h' := h
  rw [bip_adj_iff] at h'
  rcases h' with ⟨i', j', rfl, rfl, hij⟩ | ⟨i', j', rfl, rfl, hij⟩
  · have : ∀ i j, 1 / phi N ĵ (Sum.inl i) * (N.mu i j * ed (Sum.inl i') (Sum.inr j') i j) =
        if i = i' ∧ j = j' then N.mu i' j' / phi N ĵ (Sum.inl i') else 0 := by
      intro i j
      by_cases hh : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hh; simp [ed]; ring
      · rw [if_neg hh]
        simp only [ed, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, if_false, sub_zero]
        rw [if_neg (fun h2 => hh ⟨h2.1.symm, h2.2.symm⟩)]; simp
    simp only [this, ite_and]
    simp [Q, mu_div_phi N ĵ hij]
  · have : ∀ i j, 1 / phi N ĵ (Sum.inl i) * (N.mu i j * ed (Sum.inr j') (Sum.inl i') i j) =
        if i = i' ∧ j = j' then -(N.mu i' j' / phi N ĵ (Sum.inl i')) else 0 := by
      intro i j
      by_cases hh : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hh; simp [ed]; ring
      · rw [if_neg hh]
        simp only [ed, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, if_false, zero_sub]
        rw [if_neg (fun h2 => hh ⟨h2.2.symm, h2.1.symm⟩)]; simp
    simp only [this, ite_and]
    simp [Q, mu_div_phi N ĵ hij]

theorem pfw_weighted (N : TreeNetwork I J) (ĵ : Fin J) {a b : Fin I ⊕ Fin J}
    (w : (bipGraph N.adj).Walk a b) :
    ∑ i, ∑ j, 1 / phi N ĵ (Sum.inl i) * (N.mu i j * pfw N.adj w i j) = Q N ĵ b - Q N ĵ a := by
  induction w with
  | nil => simp [pfw]
  | cons h p ih =>
    simp only [pfw, Pi.add_apply, mul_add, Finset.sum_add_distrib, ih, ed_weighted N ĵ h]
    ring

/-- `cᵀ B₁ = eᵀ` with `c_i = 1/φ(i)`. -/
theorem c_B1 (N : TreeNetwork I J) (ĵ : Fin J) (k : Fin I) :
    ∑ i, 1 / phi N ĵ (Sum.inl i) * B1 N ĵ i k = 1 := by
  obtain ⟨w⟩ := N.isTree.isConnected.preconnected (Sum.inl k) (Sum.inr ĵ)
  unfold B1
  rw [flowMap_single N k ĵ w]
  simp only [Finset.mul_sum]
  rw [pfw_weighted N ĵ w]
  simp [Q, phi_root]

theorem B1_det_ne (N : TreeNetwork I J) (ĵ : Fin J) : (B1 N ĵ).det ≠ 0 := by
  obtain ⟨î, hedge⟩ := exists_neighbor N ĵ
  obtain ⟨-, ⟨rk, -, hrk⟩, hdiag, -, -⟩ := proposition_2 N î ĵ hedge
  have hlt : ((B1 N ĵ).submatrix rk.symm rk.symm).IsLowerTriangular := by
    intro a b hab
    simp only [submatrix_apply]
    apply hrk
    simpa using hab
  rw [← det_submatrix_equiv_self rk.symm, det_of_isLowerTriangular _ hlt]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => (hdiag _).ne'

/-- `eᵀB₁⁻¹ = c`. -/
theorem colsum_inv (N : TreeNetwork I J) (ĵ : Fin J) (ℓ : Fin I) :
    ∑ k, (B1 N ĵ)⁻¹ k ℓ = 1 / phi N ĵ (Sum.inl ℓ) := by
  set c : Fin I → ℝ := fun i => 1 / phi N ĵ (Sum.inl i) with hc
  have hcB : c ᵥ* B1 N ĵ = fun _ => 1 := by
    funext k; simp only [vecMul, dotProduct, hc]; exact c_B1 N ĵ k
  have hu : IsUnit (B1 N ĵ).det := isUnit_iff_ne_zero.mpr (B1_det_ne N ĵ)
  have h1 : c = (fun _ => (1 : ℝ)) ᵥ* (B1 N ĵ)⁻¹ := by
    rw [← hcB, vecMul_vecMul, mul_nonsing_inv _ hu, vecMul_one]
  have := congrFun h1 ℓ
  simp only [vecMul, dotProduct, one_mul, hc] at this
  exact this.symm

end SWSSGainAux

open SWSSNet.Diffusion SWSSGainAux

theorem solution {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) :
    (∀ i ℓ : Fin I, gain N (Sum.inl i) (Sum.inl ℓ) =
      (∑ k, (B1 N ĵ)⁻¹ k ℓ) / (∑ k, (B1 N ĵ)⁻¹ k i)) ∧
    ∀ i : Fin I, 0 < ∑ k, (B1 N ĵ)⁻¹ k i := by
  refine ⟨fun i ℓ => ?_, fun i => ?_⟩
  · rw [colsum_inv, colsum_inv, gain_ratio N ĵ]
    have := phi_pos N ĵ (Sum.inl i)
    have := phi_pos N ĵ (Sum.inl ℓ)
    field_simp
  · rw [colsum_inv]; exact one_div_pos.mpr (phi_pos N ĵ _)
