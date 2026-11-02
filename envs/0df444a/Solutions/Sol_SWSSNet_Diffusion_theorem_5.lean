-- Prove2me | solution 1 for SWSSNet.Diffusion.theorem_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:31:54.050938+00:00
-- url     : https://prove2.me/submissions/7f871912-811c-4a30-9e55-af5813f1b41a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network
import Definitions.Def_SWSSNet_Diffusion_Process
import Theorems.Thm_SWSSNet_Diffusion_atar_prop_A_2
import Theorems.Thm_SWSSNet_Diffusion_proposition_2
import Theorems.Thm_BrownianLLN_tendsto_div_atTop
import Theorems.Thm_SWSSNet_Diffusion_theorem_5_null
import Theorems.Thm_SWSSNet_Diffusion_theorem_4

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


theorem phi_class (N : TreeNetwork I J) (ĵ : Fin J) {i : Fin I} {j : Fin J} (h : N.adj i j) :
    phi N ĵ (Sum.inl i) = N.mu i j * phi N ĵ (Sum.inr j) := by
  have hadj : (bipGraph N.adj).Adj (Sum.inl i) (Sum.inr j) := by
    rw [bip_adj_iff]; exact Or.inl ⟨i, j, rfl, rfl, h⟩
  rw [phi_local N ĵ hadj]; rfl

/-- The optimal value of (LP′) in potential form. -/
noncomputable def vstar (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) : ℝ :=
  (∑ j, theta N j / phi N ĵ (Sum.inr j) - ∑ i, N.lamHat i / phi N ĵ (Sum.inl i)) /
    ∑ i, p i / phi N ĵ (Sum.inl i)

theorem denom_pos' (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    0 < ∑ i, p i / phi N ĵ (Sum.inl i) := by
  obtain ⟨i0⟩ := exists_class N ĵ
  exact Finset.sum_pos (fun i _ => div_pos (hp.1 i) (phi_pos N ĵ _)) ⟨i0, Finset.mem_univ _⟩

theorem lp_greatest (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    IsGreatest {ϑ | lpFeasible N p ϑ} (vstar N ĵ p) := by
  have hP := denom_pos' N ĵ p hp
  set P := ∑ i, p i / phi N ĵ (Sum.inl i) with hPdef
  set ϑ := vstar N ĵ p with hϑ
  constructor
  · -- attainment via a balanced flow
    set α : Fin I → ℝ := fun i => (N.lamHat i + ϑ * p i) / phi N ĵ (Sum.inl i) with hα
    set β : Fin J → ℝ := fun j => theta N j / phi N ĵ (Sum.inr j) with hβ
    have hD : ∑ i, α i = ∑ j, β j := by
      simp only [hα, hβ, add_div, Finset.sum_add_distrib, mul_div_assoc, ← Finset.mul_sum]
      rw [hϑ, vstar, ← hPdef]
      field_simp
      ring
    obtain ⟨z, ⟨hz0, hzr, hzc⟩, -⟩ := atar_prop_A_2 N α β hD
    refine ⟨fun i j => z i j * phi N ĵ (Sum.inr j), fun i j h => by simp [hz0 i j h], fun i => ?_,
      fun j => ?_⟩
    · have hrow : ∑ j, N.mu i j * (z i j * phi N ĵ (Sum.inr j)) =
          phi N ĵ (Sum.inl i) * ∑ j, z i j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : N.adj i j
        · rw [phi_class N ĵ h]; ring
        · simp [hz0 i j h]
      rw [hrow, hzr i, hα]
      have := phi_pos N ĵ (Sum.inl i)
      field_simp
      linarith
    · rw [← Finset.sum_mul, hzc j, hβ]
      have := phi_pos N ĵ (Sum.inr j)
      field_simp
  · -- upper bound by weak duality
    rintro t ⟨κ, hκ0, hκr, hκc⟩
    have hterm : ∀ i j, N.mu i j * κ i j / phi N ĵ (Sum.inl i) =
        κ i j / phi N ĵ (Sum.inr j) := by
      intro i j
      by_cases h : N.adj i j
      · rw [phi_class N ĵ h]
        have := phi_pos N ĵ (Sum.inr j)
        have := N.mu_pos i j h
        field_simp
      · simp [hκ0 i j h]
    have hsum : ∑ i, N.lamHat i / phi N ĵ (Sum.inl i) ≤
        ∑ i, (∑ j, N.mu i j * κ i j - t * p i) / phi N ĵ (Sum.inl i) :=
      Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hκr i) (phi_pos N ĵ _).le
    have hrw : ∑ i, (∑ j, N.mu i j * κ i j - t * p i) / phi N ĵ (Sum.inl i) =
        ∑ j, theta N j / phi N ĵ (Sum.inr j) - t * P := by
      simp only [sub_div, Finset.sum_sub_distrib, Finset.sum_div, hterm, mul_div_assoc,
        ← Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_div, hκc j]
    rw [hrw] at hsum
    show t ≤ vstar N ĵ p
    rw [vstar, ← hPdef, le_div_iff₀ hP]
    linarith

theorem swss_eq (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    swss N p = vstar N ĵ p :=
  (lp_greatest N ĵ p hp).csSup_eq


/-- The flow `Ψ(0, e_l − e_ĵ)` is the flow of any walk from pool `ĵ` to pool `l`. -/
theorem flowMap_pool (N : TreeNetwork I J) (ĵ l : Fin J)
    (w : (bipGraph N.adj).Walk (Sum.inr ĵ) (Sum.inr l)) :
    flowMap N 0 (Pi.single l 1 - Pi.single ĵ 1) = pfw N.adj w := by
  apply flowMap_eq N (by simp [Finset.sum_sub_distrib])
  refine ⟨fun i j hn => pfw_supp N.adj w i j hn, fun i => ?_, fun j => ?_⟩
  · rw [pfw_row]; simp
  · rw [pfw_col]
    by_cases h1 : j = l
    · subst h1
      by_cases h2 : j = ĵ
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · by_cases h2 : j = ĵ
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem c_B2 (N : TreeNetwork I J) (ĵ l : Fin J) :
    ∑ k, 1 / phi N ĵ (Sum.inl k) * B2 N ĵ k l = 1 / phi N ĵ (Sum.inr l) - 1 := by
  obtain ⟨w⟩ := N.isTree.isConnected.preconnected (Sum.inr ĵ) (Sum.inr l)
  unfold B2
  rw [flowMap_pool N ĵ l w]
  simp only [Finset.mul_sum]
  rw [pfw_weighted N ĵ w]
  simp [Q, phi_root]


/-- A tree network has at least one pool. -/
theorem exists_pool (N : TreeNetwork I J) : Nonempty (Fin J) := by
  obtain ⟨v⟩ := N.isTree.connected.nonempty
  rcases v with i | j
  · by_contra hJ
    have hJ0 : J = 0 := by
      rcases Nat.eq_zero_or_pos J with h | h
      · exact h
      · exact absurd ⟨⟨0, h⟩⟩ hJ
    subst hJ0
    have h1 := N.xi_crp.1.2.2 i
    have h2 := N.lam_pos i
    simp at h1
    linarith
  · exact ⟨j⟩

/-- The `c`-weighted drift is bounded below by `⟨c, h⟩`. -/
theorem drift_lower (N : TreeNetwork I J) (ĵ : Fin J) (u : (Fin I → ℝ) × (Fin J → ℝ))
    (hu : IsControlValue u) (y : EthierKurtz.SDEState I) :
    ∑ k, 1 / phi N ĵ (Sum.inl k) * hvec N k ≤
      ∑ k, 1 / phi N ĵ (Sum.inl k) * driftH N (hvec N) u y k := by
  obtain ⟨î, hedge⟩ := exists_neighbor N ĵ
  rw [(proposition_2 N î ĵ hedge).1 (hvec N) u y hu]
  set c : Fin I → ℝ := fun k => 1 / phi N ĵ (Sum.inl k) with hc
  set m := ∑ l, y l with hm
  set a : Fin I → ℝ := fun k => y k - max m 0 * u.1 k with ha
  set n := max (-m) 0 with hn
  have hs1 : ∑ k, u.1 k = 1 := hu.1.2
  have hs2 : ∑ l, u.2 l = 1 := hu.2.2
  have hcB1 : ∑ k, c k * (B1 N ĵ *ᵥ a) k = ∑ l, a l := by
    simp only [mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    calc ∑ k, c k * (B1 N ĵ k l * a l) = (∑ k, c k * B1 N ĵ k l) * a l := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = a l := by rw [c_B1 N ĵ l, one_mul]
  have hcB2 : ∑ k, c k * (B2 N ĵ *ᵥ u.2) k = ∑ l, (1 / phi N ĵ (Sum.inr l) - 1) * u.2 l := by
    simp only [mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← c_B2 N ĵ l, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hsa : ∑ l, a l = -n := by
    simp only [ha, Finset.sum_sub_distrib, ← Finset.mul_sum, hs1, mul_one, ← hm, hn]
    rcases le_total m 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hn0 : 0 ≤ n := le_max_right _ _
  have hpsi : 0 ≤ ∑ l, 1 / phi N ĵ (Sum.inr l) * u.2 l :=
    Finset.sum_nonneg fun l _ => mul_nonneg (one_div_pos.mpr (phi_pos N ĵ _)).le (hu.2.1 l)
  have hexp : ∑ k, c k * (WithLp.toLp 2 (hvec N - B1 N ĵ *ᵥ a + n • (B2 N ĵ *ᵥ u.2)) :
      EthierKurtz.SDEState I) k =
      ∑ k, c k * hvec N k - ∑ k, c k * (B1 N ĵ *ᵥ a) k + n * ∑ k, c k * (B2 N ĵ *ᵥ u.2) k := by
    simp only [PiLp.toLp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hexp, hcB1, hcB2, hsa]
  have : ∑ l, (1 / phi N ĵ (Sum.inr l) - 1) * u.2 l = ∑ l, 1 / phi N ĵ (Sum.inr l) * u.2 l - 1 := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hs2]
  rw [this]
  nlinarith

theorem colsum_mulVec (N : TreeNetwork I J) (ĵ : Fin J) (v : Fin I → ℝ) :
    ∑ i, ((B1 N ĵ)⁻¹ *ᵥ v) i = ∑ k, 1 / phi N ĵ (Sum.inl k) * v k := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, colsum_inv]

theorem delta_pos (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) (hp : IsPosProb p)
    (hneg : swss N p < 0) : 0 < ∑ k, 1 / phi N ĵ (Sum.inl k) * hvec N k := by
  have h4 := theorem_4 N ĵ p hp
  rw [colsum_mulVec, colsum_mulVec] at h4
  have hd : 0 < ∑ k, 1 / phi N ĵ (Sum.inl k) * p k := by
    have := denom_pos' N ĵ p hp
    simpa [div_eq_mul_inv, mul_comm] using this
  rw [h4, div_neg_iff] at hneg
  rcases hneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · linarith

/-- The drift under a Markov control is a continuous function of the control value and state. -/
noncomputable def Gd (N : TreeNetwork I J) (ĵ : Fin J) (w : ((Fin I → ℝ) × (Fin J → ℝ)) × EthierKurtz.SDEState I) :
    EthierKurtz.SDEState I :=
  WithLp.toLp 2 (hvec N - B1 N ĵ *ᵥ (fun k => w.2 k - max (∑ l, w.2 l) 0 * w.1.1 k)
    + max (-(∑ k, w.2 k)) 0 • (B2 N ĵ *ᵥ w.1.2))

theorem Gd_cont (N : TreeNetwork I J) (ĵ : Fin J) : Continuous (Gd N ĵ) := by
  unfold Gd
  apply (PiLp.continuous_toLp 2 _).comp
  apply Continuous.add
  · apply Continuous.sub continuous_const
    apply Continuous.matrix_mulVec continuous_const
    refine continuous_pi fun k => ?_
    apply Continuous.sub
    · exact (PiLp.continuous_apply 2 _ k).comp continuous_snd
    · apply Continuous.mul
      · apply Continuous.max _ continuous_const
        exact continuous_finset_sum _ fun l _ => (PiLp.continuous_apply 2 _ l).comp continuous_snd
      · exact (continuous_apply k).comp (continuous_fst.comp continuous_fst)
  · refine Continuous.smul (f := fun w : ((Fin I → ℝ) × (Fin J → ℝ)) × EthierKurtz.SDEState I =>
        max (-(∑ k, w.2 k)) 0) ?_ ?_
    · apply Continuous.max _ continuous_const
      exact (continuous_finset_sum _ fun l _ =>
        (PiLp.continuous_apply 2 _ l).comp continuous_snd).neg
    · exact Continuous.matrix_mulVec continuous_const (continuous_snd.comp continuous_fst)

theorem markovDrift_eq (N : TreeNetwork I J) (ĵ : Fin J)
    (v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ)) (hv : IsMarkovControl v) :
    markovDrift N (hvec N) v = fun y => Gd N ĵ (v y, y) := by
  obtain ⟨î, hedge⟩ := exists_neighbor N ĵ
  funext y
  exact (proposition_2 N î ĵ hedge).1 (hvec N) (v y) y (hv.2 y)

theorem drift_intInt (N : TreeNetwork I J) (ĵ : Fin J)
    (v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ)) (hv : IsMarkovControl v)
    (γ : ℝ≥0 → EthierKurtz.SDEState I) (hγ : Continuous γ) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => markovDrift N (hvec N) v (γ (Real.toNNReal s)))
      MeasureTheory.volume 0 t := by
  rw [markovDrift_eq N ĵ v hv]
  set K := (stdSimplex ℝ (Fin I) ×ˢ stdSimplex ℝ (Fin J)) ×ˢ (γ '' Set.Icc 0 (|t|).toNNReal)
    with hKdef
  have hK : IsCompact K :=
    ((isCompact_stdSimplex (𝕜 := ℝ) (Fin I)).prod (isCompact_stdSimplex (𝕜 := ℝ) (Fin J))).prod
      (isCompact_Icc.image hγ)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (Gd_cont N ĵ).continuousOn
  have hγm : Measurable fun s : ℝ => γ (Real.toNNReal s) :=
    hγ.measurable.comp measurable_real_toNNReal
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := C) ?_ ?_ ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
  · exact ((Gd_cont N ĵ).measurable.comp ((hv.1.comp hγm).prodMk hγm)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => hC _ ?_
    have hv2 := hv.2 (γ (Real.toNNReal s))
    refine ⟨⟨hv2.1, hv2.2⟩, ⟨Real.toNNReal s, ⟨zero_le, ?_⟩, rfl⟩⟩
    rw [Set.mem_uIoc] at hs
    apply Real.toNNReal_le_toNNReal
    rcases hs with ⟨_, h⟩ | ⟨_, h⟩
    · exact h.trans (le_abs_self t)
    · linarith [abs_nonneg t, neg_abs_le t]

end SWSSGainAux

open SWSSNet.Diffusion SWSSGainAux Filter Topology

theorem transient_part {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p)
    (hneg : swss N p < 0) (v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ))
    (hv : IsMarkovControl v) : IsTransient (markovDrift N (hvec N) v) (Sigma N) := by
  intro Ω _ Pr _ B X x hB hX
  obtain ⟨ĵ⟩ := exists_pool N
  obtain ⟨i0⟩ := exists_class N ĵ
  set c : Fin I → ℝ := fun k => 1 / phi N ĵ (Sum.inl k) with hcdef
  have hc : ∀ k, 0 < c k := fun k => one_div_pos.mpr (phi_pos N ĵ _)
  set δ := ∑ k, c k * hvec N k with hδdef
  have hδ : 0 < δ := delta_pos N ĵ p hp hneg
  set a : Fin I → ℝ := fun k => c k * Real.sqrt (2 * N.lam k) with hadef
  set ℓ : EthierKurtz.SDEState I →L[ℝ] ℝ :=
    ∑ k, c k • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin I => ℝ) k) with hℓ
  have hℓapp : ∀ y : EthierKurtz.SDEState I, ℓ y = ∑ k, c k * y k := by
    intro y; simp [hℓ, _root_.sum_apply]
  have hlln : ∀ᵐ ω ∂Pr, ∀ k, Tendsto (fun t : ℝ≥0 => B t ω k / t) atTop (𝓝 0) :=
    ae_all_iff.mpr fun k => BrownianLLN.tendsto_div_atTop (hB.2.2.1 k)
  filter_upwards [hlln] with ω hω
  -- the linear functional grows at least linearly
  have hZ : ∀ t : ℝ≥0, ℓ x + δ * t + ∑ k, a k * B t ω k ≤ ℓ (X t ω) := by
    intro t
    have hsde := hX.1.2 ω t
    have hint := drift_intInt N ĵ v hv (fun s => X s ω) (hX.1.1 ω) t
    have hI : δ * t ≤ ℓ (∫ s in (0 : ℝ)..(t : ℝ), markovDrift N (hvec N) v (X (Real.toNNReal s) ω)) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm ℓ hint]
      have hconst : ∫ s in (0 : ℝ)..(t : ℝ), δ = δ * t := by simp [mul_comm]
      rw [← hconst]
      refine intervalIntegral.integral_mono_on (NNReal.coe_nonneg t) (by simp) ?_ fun s _ => ?_
      · exact ⟨ℓ.integrable_comp hint.1, ℓ.integrable_comp hint.2⟩
      · rw [hℓapp]
        exact drift_lower N ĵ (v _) (hv.2 _) _
    have hmv : ℓ (GPhNGIDiffusion.EMError.mv (Sigma N) (B t ω)) = ∑ k, a k * B t ω k := by
      rw [hℓapp]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [GPhNGIDiffusion.EMError.mv, SWSSNet.Diffusion.Sigma, mulVec_diagonal, hadef]
      ring
    rw [hsde, map_add, map_add, hmv]
    linarith
  -- asymptotics
  set Cs := ∑ k, c k with hCs
  have hCs0 : 0 < Cs := Finset.sum_pos (fun k _ => hc k) ⟨i0, Finset.mem_univ _⟩
  have hnorm : ∀ y : EthierKurtz.SDEState I, ℓ y ≤ Cs * ‖y‖ := by
    intro y
    rw [hℓapp, hCs, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 : y k ≤ ‖y‖ := (le_abs_self _).trans (by simpa using PiLp.norm_apply_le y k)
    exact mul_le_mul_of_nonneg_left h1 (hc k).le
  have hg : Tendsto (fun t : ℝ≥0 => ∑ k, a k * (B t ω k / t)) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin I))
      (fun k _ => (hω k).const_mul (a k))
    simpa using this
  have hev : ∀ᶠ t : ℝ≥0 in atTop, ∑ k, a k * (B t ω k / t) ∈ Set.Ioo (-(δ / 2)) (δ / 2) :=
    hg.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have hlow : ∀ᶠ t : ℝ≥0 in atTop, (ℓ x + δ / 2 * t) / Cs ≤ ‖X t ω‖ := by
    filter_upwards [hev, eventually_ge_atTop (1 : ℝ≥0)] with t ht ht1
    have htpos : (0 : ℝ) < t := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      linarith
    have hsum : ∑ k, a k * B t ω k = t * ∑ k, a k * (B t ω k / t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    have h1 := hZ t
    have h2 := hnorm (X t ω)
    rw [div_le_iff₀ hCs0]
    have h3 : -(δ / 2) * t ≤ ∑ k, a k * B t ω k := by
      rw [hsum]
      have := ht.1
      nlinarith
    nlinarith
  refine tendsto_atTop_mono' atTop hlow ?_
  apply Tendsto.atTop_div_const hCs0
  apply tendsto_atTop_add_const_left
  exact Tendsto.const_mul_atTop (half_pos hδ) (NNReal.tendsto_coe_atTop.mpr tendsto_id)

theorem solution {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    (swss N p < 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      IsTransient (markovDrift N (hvec N) v) (SWSSNet.Diffusion.Sigma N)) ∧
    (swss N p = 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      ∀ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (hvec N) v) (SWSSNet.Diffusion.Sigma N) P →
        ¬ ∃ π, GPhNGIDiffusion.EMError.IsInvariantMeasure P π) :=
  ⟨fun hneg v hv => transient_part N p hp hneg v hv, theorem_5_null N p hp⟩
