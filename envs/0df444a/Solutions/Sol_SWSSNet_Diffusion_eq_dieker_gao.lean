-- Prove2me | solution 1 for SWSSNet.Diffusion.eq_dieker_gao
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:19:27.753095+00:00
-- url     : https://prove2.me/submissions/4b0220f5-6a6a-48af-9130-df2c65717b56

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



theorem quad (n : ℕ) (S M : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = S) (x : Fin n → ℝ) :
    x ⬝ᵥ ((S * M + Mᵀ * S) *ᵥ x) = 2 * ((S *ᵥ x) ⬝ᵥ (M *ᵥ x)) := by
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x S,
    dotProduct_mulVec x Mᵀ, vecMul_transpose]
  have : x ᵥ* S = S *ᵥ x := by
    conv_lhs => rw [← hS]
    rw [vecMul_transpose]
  rw [this, dotProduct_comm (M *ᵥ x)]
  ring

theorem amgm (ε : ℝ) (hε : 0 < ε) (p q : ℝ) : 2 * |p * q| ≤ ε * p ^ 2 + q ^ 2 / ε := by
  rw [abs_mul]
  have h := sq_nonneg (ε * |p| - |q|)
  have e : ε * p ^ 2 + q ^ 2 / ε - 2 * (|p| * |q|) = (ε * |p| - |q|) ^ 2 / ε := by
    rw [← sq_abs p, ← sq_abs q]; field_simp; ring
  have := div_nonneg h hε.le
  linarith


theorem prod_bound (ci u sx r R C2 I' : ℝ) (hci : 0 < ci) (hR : 0 ≤ R) (hs2 : sx ^ 2 ≤ C2 * R)
    (hr2 : r ^ 2 ≤ I' * R) :
    ci ^ 2 / 2 * u ^ 2 - (ci ^ 2 * I' + C2 + ci * (C2 + I') / 2) * R ≤
      ci * ((ci * u + sx) * (u + r)) := by
  have h1 : 0 ≤ ci ^ 2 * (u / 2 + r) ^ 2 := by positivity
  have h2 : 0 ≤ (ci * u / 2 + sx) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ ci * (sx + r) ^ 2 := mul_nonneg hci.le (sq_nonneg _)
  have h4 : ci ^ 2 * r ^ 2 ≤ ci ^ 2 * (I' * R) := mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)
  have h5 : ci * sx ^ 2 ≤ ci * (C2 * R) := mul_le_mul_of_nonneg_left hs2 hci.le
  have h6 : ci * r ^ 2 ≤ ci * (I' * R) := mul_le_mul_of_nonneg_left hr2 hci.le
  have e : ci * ((ci * u + sx) * (u + r)) = ci ^ 2 * u ^ 2 + ci ^ 2 * (u * r) + ci * (u * sx)
      + ci * (sx * r) := by ring
  have e1 : ci ^ 2 * (u / 2 + r) ^ 2 = ci ^ 2 * u ^ 2 / 4 + ci ^ 2 * (u * r) + ci ^ 2 * r ^ 2 := by ring
  have e2 : (ci * u / 2 + sx) ^ 2 = ci ^ 2 * u ^ 2 / 4 + ci * (u * sx) + sx ^ 2 := by ring
  have e3 : ci * (sx + r) ^ 2 = ci * sx ^ 2 + 2 * (ci * (sx * r)) + ci * r ^ 2 := by ring
  rw [e]
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  nlinarith [h1, h2, h3, h4, h5, h6, hs2]

/-- Diagonal Lyapunov weights for a matrix that is lower triangular in some ordering, with
positive diagonal, after deleting the last class `î`. -/
theorem diag_weights {I : ℕ} (B : Matrix (Fin I) (Fin I) ℝ) (î : Fin I) (rk : Fin I ≃ Fin I)
    (hlast : ∀ k, rk k ≤ rk î) (hrk : ∀ k l, rk k < rk l → B k l = 0) (hdiag : ∀ i, 0 < B i i) :
    ∃ d : Fin I → ℝ, (∀ k, 0 ≤ d k) ∧ d î = 0 ∧ (∀ k, k ≠ î → 0 < d k) ∧ ∃ a : ℝ, 0 < a ∧
      ∀ x : Fin I → ℝ, a * ∑ k ∈ Finset.univ.erase î, x k ^ 2 ≤ ∑ k, d k * x k * (B *ᵥ x) k := by
  classical
  have hBî : ∀ k, k ≠ î → B k î = 0 := fun k hk =>
    hrk k î (lt_of_le_of_ne (hlast k) (fun h => hk (rk.injective h)))
  have hoff : ∀ k l, k ≠ î → B k l ≠ 0 → k ≠ l → l ≠ î ∧ rk l < rk k := by
    intro k l hk hB hkl
    refine ⟨fun h => hB (h ▸ hBî k hk), ?_⟩
    rcases lt_trichotomy (rk l) (rk k) with h | h | h
    · exact h
    · exact absurd (rk.injective h).symm hkl
    · exact absurd (hrk k l h) hB
  -- constants
  have hne : (Finset.univ : Finset (Fin I)).Nonempty := ⟨î, Finset.mem_univ _⟩
  set b := Finset.univ.inf' hne (fun k => B k k) with hbdef
  have hbk : ∀ k, b ≤ B k k := fun k => Finset.inf'_le _ (Finset.mem_univ k)
  have hb : 0 < b := by
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' hne (fun k => B k k)
    rw [hbdef, hk]; exact hdiag k
  set Mx := ∑ k, ∑ l, |B k l| + 1 with hMxdef
  have hrow : ∀ k, ∑ l, |B k l| ≤ Mx := by
    intro k
    have h1 : ∑ l, |B k l| ≤ ∑ k, ∑ l, |B k l| := Finset.single_le_sum (f := fun k => ∑ l, |B k l|)
      (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (B k l)) (Finset.mem_univ k)
    linarith
  have hcol : ∀ l, ∑ k, |B k l| ≤ Mx := by
    intro l
    have h1 : ∀ k, |B k l| ≤ ∑ l', |B k l'| := fun k =>
      Finset.single_le_sum (f := fun l' => |B k l'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    have : ∑ k, |B k l| ≤ ∑ k, ∑ l', |B k l'| := Finset.sum_le_sum fun k _ => h1 k
    linarith
  have hMx : 0 < Mx := by
    have : 0 ≤ ∑ k, ∑ l, |B k l| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hbM : b ≤ Mx := by
    have h1 : B î î ≤ |B î î| := le_abs_self _
    have h2 : |B î î| ≤ ∑ l, |B î l| :=
      Finset.single_le_sum (f := fun l => |B î l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ î)
    linarith [hbk î, hrow î]
  set ε := b / (4 * Mx) with hεdef
  have hε : 0 < ε := by positivity
  have hεMx : ε * Mx = b / 4 := by rw [hεdef]; field_simp
  set t := ε * b / (4 * Mx) with htdef
  have ht : 0 < t := by positivity
  have htM : t * Mx / ε = b / 4 := by rw [htdef]; field_simp
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]; linarith
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one (by positivity)]
    nlinarith
  set d : Fin I → ℝ := fun k => if k = î then 0 else t ^ (rk k : ℕ) with hddef
  have hd0 : ∀ k, 0 ≤ d k := by
    intro k; simp only [hddef]; split_ifs
    · exact le_rfl
    · positivity
  have hdî : d î = 0 := by simp [hddef]
  have hdle : ∀ k l, B k l ≠ 0 → k ≠ l → d k ≤ t * d l := by
    intro k l hB hkl
    by_cases hk : k = î
    · rw [hk, hdî]; exact mul_nonneg ht.le (hd0 l)
    · obtain ⟨hl, hlt⟩ := hoff k l hk hB hkl
      simp only [hddef, if_neg hk, if_neg hl]
      rw [← pow_succ']
      exact pow_le_pow_of_le_one ht.le ht1 (by exact hlt)
  have hdlow : ∀ k, k ≠ î → t ^ I ≤ d k := by
    intro k hk
    simp only [hddef, if_neg hk]
    exact pow_le_pow_of_le_one ht.le ht1 (by have := (rk k).isLt; omega)
  -- the main lower bound
  have hF : ∀ x : Fin I → ℝ, (3 * b / 4) * ∑ k, d k * x k ^ 2 ≤ ∑ k, d k * x k * (B *ᵥ x) k := by
    intro x
    have hterm : ∀ k l, (if k = l then d k * B k k * x k ^ 2 else 0)
        - (ε / 2 * d k * |B k l| * x k ^ 2 + t / (2 * ε) * d l * |B k l| * x l ^ 2)
        ≤ d k * x k * (B k l * x l) := by
      intro k l
      have hA : 0 ≤ ε / 2 * d k * |B k l| * x k ^ 2 := by
        have := hd0 k; positivity
      have hB' : 0 ≤ t / (2 * ε) * d l * |B k l| * x l ^ 2 := by
        have := hd0 l; positivity
      by_cases hkl : k = l
      · subst hkl; simp only [if_true]; nlinarith
      · rw [if_neg hkl]
        by_cases hB0 : B k l = 0
        · rw [hB0]; simp only [zero_mul, mul_zero]; linarith
        · have hdkl := hdle k l hB0 hkl
          have h1 : -(|B k l| * |x k * x l|) ≤ B k l * (x k * x l) := by
            have := neg_abs_le (B k l * (x k * x l)); rwa [abs_mul] at this
          have h2 := amgm ε hε (x k) (x l)
          have h3 : d k * x l ^ 2 / ε ≤ t * d l * x l ^ 2 / ε := by
            apply div_le_div_of_nonneg_right _ hε.le
            exact mul_le_mul_of_nonneg_right hdkl (sq_nonneg _)
          have hdk := hd0 k
          have habs := abs_nonneg (B k l)
          have h4 : d k * |B k l| * (2 * |x k * x l|) ≤
              d k * |B k l| * (ε * x k ^ 2 + x l ^ 2 / ε) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hdk habs)
          have h5 : t / (2 * ε) * d l * |B k l| * x l ^ 2 = |B k l| * (t * d l * x l ^ 2 / ε) / 2 := by
            field_simp
          have h6 : d k * |B k l| * (x l ^ 2 / ε) = |B k l| * (d k * x l ^ 2 / ε) := by ring
          have h7 : |B k l| * (d k * x l ^ 2 / ε) ≤ |B k l| * (t * d l * x l ^ 2 / ε) :=
            mul_le_mul_of_nonneg_left h3 habs
          have h8 : d k * x k * (B k l * x l) = d k * (B k l * (x k * x l)) := by ring
          rw [h8, h5]
          nlinarith [mul_le_mul_of_nonneg_left h1 hdk]
    have hsum : ∑ k, d k * x k * (B *ᵥ x) k = ∑ k, ∑ l, d k * x k * (B k l * x l) := by
      simp only [mulVec, dotProduct, Finset.mul_sum]
    rw [hsum]
    have hlow := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm k l
    refine le_trans ?_ hlow
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    have e1 : ∑ k, ∑ l, ε / 2 * d k * |B k l| * x k ^ 2 = ∑ k, ε / 2 * d k * x k ^ 2 * ∑ l, |B k l| := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ k, ∑ l, t / (2 * ε) * d l * |B k l| * x l ^ 2 =
        ∑ l, t / (2 * ε) * d l * x l ^ 2 * ∑ k, |B k l| := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have b1 : ∑ k, ε / 2 * d k * x k ^ 2 * ∑ l, |B k l| ≤ ∑ k, ε / 2 * d k * x k ^ 2 * Mx :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hrow k) (by have := hd0 k; positivity)
    have b2 : ∑ l, t / (2 * ε) * d l * x l ^ 2 * ∑ k, |B k l| ≤ ∑ l, t / (2 * ε) * d l * x l ^ 2 * Mx :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hcol l) (by have := hd0 l; positivity)
    have b3 : ∑ k, d k * b * x k ^ 2 ≤ ∑ k, d k * B k k * x k ^ 2 :=
      Finset.sum_le_sum fun k _ => by
        have := hd0 k
        have := hbk k
        have := sq_nonneg (x k)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbk k) (hd0 k)) (sq_nonneg _)
    have e3 : ∑ k, ε / 2 * d k * x k ^ 2 * Mx = (ε * Mx / 2) * ∑ k, d k * x k ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have e4 : ∑ l, t / (2 * ε) * d l * x l ^ 2 * Mx = (t * Mx / ε / 2) * ∑ k, d k * x k ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => ?_; field_simp
    have e5 : ∑ k, d k * b * x k ^ 2 = b * ∑ k, d k * x k ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2]
    rw [hεMx] at e3
    rw [htM] at e4
    linarith
  set a := (3 * b / 4) * t ^ I with hadef
  have ha : 0 < a := by positivity
  refine ⟨d, hd0, hdî, fun k hk => lt_of_lt_of_le (pow_pos ht I) (hdlow k hk), a, ha, fun x => ?_⟩
  refine le_trans ?_ (hF x)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ î), hdî, zero_mul, zero_add, hadef, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_right (hdlow k (Finset.ne_of_mem_erase hk)) (sq_nonneg _)


theorem dg_main {I : ℕ} (B : Matrix (Fin I) (Fin I) ℝ) (î : Fin I) (c : Fin I → ℝ)
    (hc : ∀ k, 0 < c k) (hcB : ∀ l, ∑ k, c k * B k l = 1) (hBî : ∀ k, k ≠ î → B k î = 0)
    (d : Fin I → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hdî : d î = 0) (hdpos : ∀ k, k ≠ î → 0 < d k)
    (a : ℝ) (ha : 0 < a)
    (hFa : ∀ x : Fin I → ℝ, a * ∑ k ∈ Finset.univ.erase î, x k ^ 2 ≤ ∑ k, d k * x k * (B *ᵥ x) k) :
    ∃ (S : Matrix (Fin I) (Fin I) ℝ) (κ : ℝ), S.PosDef ∧ 0 < κ ∧
      (S * B + Bᵀ * S - (2 * κ) • (1 : Matrix (Fin I) (Fin I) ℝ)).PosDef ∧
      (S * B * (1 - vecMulVec (Pi.single î 1) (fun _ => (1 : ℝ)))
        + (1 - vecMulVec (fun _ => (1 : ℝ)) (Pi.single î 1)) * Bᵀ * S).PosSemidef := by
  classical
  have hF0 : ∀ x : Fin I → ℝ, 0 ≤ ∑ k, d k * x k * (B *ᵥ x) k := by
    intro x
    refine le_trans ?_ (hFa x)
    exact mul_nonneg ha.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  set ci := c î with hcidef
  have hci : 0 < ci := hc î
  set C2 := ∑ k, c k ^ 2 with hC2
  have hC2pos : 0 ≤ C2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hIpos : (0 : ℝ) < I := by have := Fin.pos î; exact_mod_cast this
  set K0 := ci ^ 2 * I + C2 + ci * (C2 + I) / 2 with hK0
  have hK0pos : 0 < K0 := by
    have h1 : 0 < ci ^ 2 * I := mul_pos (pow_pos hci 2) hIpos
    have h2 : 0 ≤ ci * (C2 + I) / 2 := by
      have := mul_nonneg hci.le (add_nonneg hC2pos hIpos.le); linarith
    linarith
  set σ := a * ci / (2 * K0) with hσdef
  have hσ : 0 < σ := div_pos (mul_pos ha hci) (mul_pos two_pos hK0pos)
  set S : Matrix (Fin I) (Fin I) ℝ := diagonal d + σ • vecMulVec c c with hSdef
  have hSsymm : Sᵀ = S := by
    rw [hSdef, transpose_add, transpose_smul, diagonal_transpose, transpose_vecMulVec]
  have hSherm : S.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hSsymm]
  have hSx : ∀ x : Fin I → ℝ, S *ᵥ x = fun k => d k * x k + σ * (c k * (c ⬝ᵥ x)) := by
    intro x; funext k
    simp only [hSdef, add_mulVec, Pi.add_apply, mulVec_diagonal, smul_mulVec, Pi.smul_apply,
      smul_eq_mul]
    congr 2
    simp only [mulVec, vecMulVec, dotProduct, of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hcBy : ∀ y : Fin I → ℝ, ∑ k, c k * (B *ᵥ y) k = ∑ l, y l := by
    intro y
    simp only [mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    calc ∑ k, c k * (B k l * y l) = (∑ k, c k * B k l) * y l := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = y l := by rw [hcB l, one_mul]
  have hdotB : ∀ x y : Fin I → ℝ, (S *ᵥ x) ⬝ᵥ (B *ᵥ y) =
      ∑ k, d k * x k * (B *ᵥ y) k + σ * (c ⬝ᵥ x) * ∑ l, y l := by
    intro x y
    rw [hSx]
    simp only [dotProduct, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [← hcBy y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hstar : ∀ x : Fin I → ℝ, star x = x := fun x => by simp
  -- lower bound for the quadratic form of `SB`
  have hlow : ∀ x : Fin I → ℝ, min (a / 2) (σ * ci / 2) * ∑ k, x k ^ 2 ≤ (S *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    intro x
    rw [hdotB]
    set R := ∑ k ∈ Finset.univ.erase î, x k ^ 2 with hR
    set u := x î with hu
    set sx := ∑ k ∈ Finset.univ.erase î, c k * x k with hsx
    set r := ∑ k ∈ Finset.univ.erase î, x k with hr
    have hcx : c ⬝ᵥ x = ci * u + sx := by
      simp only [dotProduct]; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ î)]
    have hsum : ∑ l, x l = u + r := by rw [← Finset.add_sum_erase _ _ (Finset.mem_univ î)]
    have hsq : ∑ k, x k ^ 2 = u ^ 2 + R := by rw [← Finset.add_sum_erase _ _ (Finset.mem_univ î)]
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs2 : sx ^ 2 ≤ C2 * R := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase î) c x
      have h2 : ∑ k ∈ Finset.univ.erase î, c k ^ 2 ≤ C2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => sq_nonneg _
      calc sx ^ 2 ≤ (∑ k ∈ Finset.univ.erase î, c k ^ 2) * R := h1
        _ ≤ C2 * R := mul_le_mul_of_nonneg_right h2 hR0
    have hr2 : r ^ 2 ≤ I * R := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase î) (fun _ => (1 : ℝ)) x
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
      have h2 : ((Finset.univ.erase î).card : ℝ) ≤ I := by
        have := Finset.card_erase_le (s := Finset.univ) (a := î)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      calc r ^ 2 ≤ ((Finset.univ.erase î).card : ℝ) * R := h1
        _ ≤ I * R := mul_le_mul_of_nonneg_right h2 hR0
    have hprod := prod_bound ci u sx r R C2 I hci hR0 hs2 hr2
    have hσprod : σ * ci / 2 * u ^ 2 - a / 2 * R ≤ σ * ((ci * u + sx) * (u + r)) := by
      have e : σ * ((ci * u + sx) * (u + r)) = (σ / ci) * (ci * ((ci * u + sx) * (u + r))) := by
        field_simp
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left hprod (div_nonneg hσ.le hci.le)
      have e2 : σ / ci * (ci ^ 2 / 2 * u ^ 2 - K0 * R) = σ * ci / 2 * u ^ 2 - a / 2 * R := by
        rw [hσdef]; field_simp
      rw [← hK0] at h1
      linarith
    have hm1 : min (a / 2) (σ * ci / 2) ≤ a / 2 := min_le_left _ _
    have hm2 : min (a / 2) (σ * ci / 2) ≤ σ * ci / 2 := min_le_right _ _
    have hF := hFa x
    have h3 := mul_le_mul_of_nonneg_right hm1 hR0
    have h4 := mul_le_mul_of_nonneg_right hm2 (sq_nonneg u)
    rw [hcx, hsum, hsq]
    have e6 : σ * (ci * u + sx) * (u + r) = σ * ((ci * u + sx) * (u + r)) := by ring
    rw [e6]
    have e5 : min (a / 2) (σ * ci / 2) * (u ^ 2 + R) =
        min (a / 2) (σ * ci / 2) * R + min (a / 2) (σ * ci / 2) * u ^ 2 := by ring
    rw [e5]
    linarith
  set m := min (a / 2) (σ * ci / 2) with hmdef
  have hm : 0 < m := lt_min (half_pos ha) (half_pos (mul_pos hσ hci))
  refine ⟨S, m / 2, ?_, half_pos hm, ?_, ?_⟩
  · -- `S` is positive definite
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hSherm, fun x hx => ?_⟩
    rw [hstar, hSx]
    simp only [dotProduct]
    have e : ∑ k, x k * (d k * x k + σ * (c k * ∑ l, c l * x l)) =
        ∑ k, d k * x k ^ 2 + σ * (∑ l, c l * x l) ^ 2 := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => by ring
      · rw [sq, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    have h0 : 0 ≤ ∑ k, d k * x k ^ 2 := Finset.sum_nonneg fun k _ => mul_nonneg (hd0 k) (sq_nonneg _)
    by_cases hall : ∀ k, k ≠ î → x k = 0
    · have hxî : x î ≠ 0 := by
        intro h0'
        apply hx; funext k
        by_cases hk : k = î
        · rw [hk, h0']; rfl
        · exact hall k hk
      have hcx : ∑ l, c l * x l = c î * x î := by
        rw [Finset.sum_eq_single î]
        · intro k _ hk; rw [hall k hk, mul_zero]
        · simp
      rw [hcx]
      have h1 : 0 < (c î * x î) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero (hc î).ne' hxî)))
      have : 0 < σ * (c î * x î) ^ 2 := mul_pos hσ h1
      linarith
    · push Not at hall
      obtain ⟨k, hk, hxk⟩ := hall
      have h1 : d k * x k ^ 2 ≤ ∑ k, d k * x k ^ 2 :=
        Finset.single_le_sum (f := fun k => d k * x k ^ 2)
          (fun k _ => mul_nonneg (hd0 k) (sq_nonneg _)) (Finset.mem_univ k)
      have h2 : 0 < d k * x k ^ 2 :=
        mul_pos (hdpos k hk) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hxk)))
      have h3 : 0 ≤ σ * (∑ l, c l * x l) ^ 2 := mul_nonneg hσ.le (sq_nonneg _)
      linarith
  · -- strict Lyapunov inequality
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_add,
        transpose_mul, transpose_mul, transpose_transpose, hSsymm, transpose_smul, transpose_one,
        add_comm]
    · rw [hstar, sub_mulVec, dotProduct_sub, quad I S B hSsymm x, smul_mulVec, one_mulVec,
        dotProduct_smul, smul_eq_mul]
      have hxx : x ⬝ᵥ x = ∑ k, x k ^ 2 := by
        simp only [dotProduct, sq]
      have hpos : 0 < ∑ k, x k ^ 2 := by
        by_contra hle
        push Not at hle
        apply hx
        funext k
        have h0 : ∑ k, x k ^ 2 = 0 := le_antisymm hle (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h0
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h0 k (Finset.mem_univ k))
      rw [hxx]
      have h1 := hlow x
      have h2 : 0 < m * ∑ k, x k ^ 2 := mul_pos hm hpos
      have e : 2 * (m / 2) * ∑ k, x k ^ 2 = m * ∑ k, x k ^ 2 := by ring
      rw [e]
      linarith
  · -- `Φ ≥ 0`
    set P : Matrix (Fin I) (Fin I) ℝ := 1 - vecMulVec (Pi.single î 1) (fun _ => (1 : ℝ)) with hPdef
    have hPt : Pᵀ = 1 - vecMulVec (fun _ => (1 : ℝ)) (Pi.single î 1) := by
      rw [hPdef, transpose_sub, transpose_one, transpose_vecMulVec]
    have hΦ : S * B * P + (1 - vecMulVec (fun _ => (1 : ℝ)) (Pi.single î 1)) * Bᵀ * S =
        S * (B * P) + (B * P)ᵀ * S := by
      rw [transpose_mul, hPt, Matrix.mul_assoc]
    rw [hΦ, posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
      simp only [transpose_add, transpose_mul, transpose_transpose, hSsymm, Matrix.mul_assoc]
      abel
    · rw [hstar, quad I S (B * P) hSsymm x, ← mulVec_mulVec, hdotB]
      have hPx : P *ᵥ x = fun l => x l - (if l = î then ∑ k, x k else 0) := by
        funext l
        rw [hPdef, sub_mulVec, one_mulVec]
        simp only [Pi.sub_apply]
        congr 1
        simp only [mulVec, vecMulVec, dotProduct, of_apply]
        by_cases hl : l = î
        · subst hl; simp
        · simp [Pi.single_apply, hl]
      have hsumP : ∑ l, (P *ᵥ x) l = 0 := by
        rw [hPx]
        simp [Finset.sum_sub_distrib]
      have hBP : ∑ k, d k * x k * (B *ᵥ (P *ᵥ x)) k = ∑ k, d k * x k * (B *ᵥ x) k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = î
        · rw [hk, hdî]; simp
        · congr 1
          rw [hPx]
          simp only [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true, hBî k hk, zero_mul, sub_zero]
      rw [hsumP, hBP, mul_zero, add_zero]
      have := hF0 x
      linarith

end SWSSGainAux

open SWSSNet.Diffusion SWSSGainAux

theorem solution {I J : ℕ} (N : TreeNetwork I J) (î : Fin I) (ĵ : Fin J) (hedge : N.adj î ĵ) :
    ∃ (S : Matrix (Fin I) (Fin I) ℝ) (κ : ℝ), S.PosDef ∧ 0 < κ ∧
      (S * B1 N ĵ + (B1 N ĵ)ᵀ * S - (2 * κ) • (1 : Matrix (Fin I) (Fin I) ℝ)).PosDef ∧
      (S * B1 N ĵ * (1 - vecMulVec (Pi.single î 1) (fun _ => (1 : ℝ)))
        + (1 - vecMulVec (fun _ => (1 : ℝ)) (Pi.single î 1)) * (B1 N ĵ)ᵀ * S).PosSemidef := by
  obtain ⟨-, ⟨rk, hlast, hrk⟩, hdiag, -, -⟩ := proposition_2 N î ĵ hedge
  obtain ⟨d, hd0, hdî, hdpos, a, ha, hFa⟩ := diag_weights (B1 N ĵ) î rk hlast hrk hdiag
  have hBî : ∀ k, k ≠ î → B1 N ĵ k î = 0 := fun k hk =>
    hrk k î (lt_of_le_of_ne (hlast k) (fun h => hk (rk.injective h)))
  exact dg_main (B1 N ĵ) î (fun k => 1 / phi N ĵ (Sum.inl k))
    (fun k => one_div_pos.mpr (phi_pos N ĵ _)) (c_B1 N ĵ) hBî d hd0 hdî hdpos a ha hFa
