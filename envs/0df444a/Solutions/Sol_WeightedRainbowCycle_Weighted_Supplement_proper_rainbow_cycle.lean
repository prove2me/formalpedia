-- Prove2me | solution 1 for WeightedRainbowCycle.Weighted.Supplement.proper_rainbow_cycle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:46:59.176869+00:00
-- url     : https://prove2.me/submissions/6e3169ae-219c-4b2f-9b5f-239c15782b3a

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model
import Definitions.Def_WeightedRainbowCycle_Weighted_Reachability
import Definitions.Def_WeightedRainbowCycle_Weighted_Subgraph
import Theorems.Thm_WeightedRainbowCycle_Weighted_density_expansion
import Theorems.Thm_WeightedRainbowCycle_Weighted_boundary_derivative

section
set_option autoImplicit false

namespace WeightedRainbowCycle.Dev.EngineAnalysis
open DiffNeighbors.Bias

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weight_sum (p : ℝ) : ∑ z : ι → Bool, (∏ j, if z j then p else 1 - p) = 1 := by
  have h := Finset.prod_univ_sum (fun (_ : ι) => (Finset.univ : Finset Bool))
    (fun (_ : ι) (b : Bool) => if b then p else 1 - p)
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_sub_cancel,
    Finset.prod_const_one] at h
  rw [Fintype.piFinset_univ] at h
  exact h.symm

theorem bernExp_const (p c : ℝ) : bernExp p (fun _ : ι → Bool => c) = c := by
  unfold bernExp mlExt
  simp only
  rw [← Finset.sum_mul, weight_sum, one_mul]

theorem bernExp_sub (p : ℝ) (a b : (ι → Bool) → ℝ) :
    bernExp p (fun z => a z - b z) = bernExp p a - bernExp p b := by
  unfold bernExp mlExt
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem bernExp_add (p : ℝ) (a b : (ι → Bool) → ℝ) :
    bernExp p (fun z => a z + b z) = bernExp p a + bernExp p b := by
  unfold bernExp mlExt
  simp only [mul_add, Finset.sum_add_distrib]

theorem bernExp_mul_left (p c : ℝ) (a : (ι → Bool) → ℝ) :
    bernExp p (fun z => c * a z) = c * bernExp p a := by
  unfold bernExp mlExt
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => by ring)

theorem bernExp_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b : (ι → Bool) → ℝ}
    (h : ∀ z, a z ≤ b z) : bernExp p a ≤ bernExp p b := by
  unfold bernExp mlExt
  refine Finset.sum_le_sum (fun z _ => ?_)
  refine mul_le_mul_of_nonneg_left (h z) (Finset.prod_nonneg (fun j _ => ?_))
  split_ifs
  · exact hp0
  · linarith

theorem bernExp_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a : (ι → Bool) → ℝ}
    (h : ∀ z, 0 ≤ a z) : 0 ≤ bernExp p a := by
  have := bernExp_mono hp0 hp1 (a := fun _ => 0) (b := a) h
  rwa [bernExp_const] at this

theorem bernExp_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a : (ι → Bool) → ℝ} (c : ℝ)
    (h : ∀ z, a z ≤ c) : bernExp p a ≤ c := by
  have := bernExp_mono hp0 hp1 (a := a) (b := fun _ => c) h
  rwa [bernExp_const] at this

theorem bernExp_differentiable (a : (ι → Bool) → ℝ) :
    Differentiable ℝ (fun p => bernExp p a) := by
  unfold bernExp mlExt
  refine Differentiable.fun_sum (fun z _ => ?_)
  refine Differentiable.mul ?_ (differentiable_const _)
  refine Differentiable.fun_finsetProd (fun j _ => ?_)
  split_ifs
  · exact differentiable_id
  · exact (differentiable_const _).sub differentiable_id

theorem bernExp_compl_half (a : (ι → Bool) → ℝ) :
    bernExp (1 / 2) (fun z => a (fun i => !z i)) = bernExp (1 / 2) a := by
  unfold bernExp mlExt
  have hw : ∀ z : ι → Bool, (∏ j, if z j then (1 / 2 : ℝ) else 1 - 1 / 2) = (1 / 2) ^ Fintype.card ι := by
    intro z
    rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    split_ifs <;> norm_num
  simp only [hw]
  exact Equiv.sum_comp (Equiv.piCongrRight (fun _ : ι => Equiv.boolNot))
    (fun z => (1 / 2 : ℝ) ^ Fintype.card ι * a z)

/-- The differential inequality `f' ≤ -κ f` on `(q0, 1/2)` gives exponential decay. -/
theorem ode_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f) (κ q0 : ℝ) (hq0 : q0 ≤ 1 / 2)
    (h : ∀ q, q0 < q → q < 1 / 2 → deriv f q ≤ -κ * f q) :
    f (1 / 2) ≤ f q0 * Real.exp (-κ * (1 / 2 - q0)) := by
  let g : ℝ → ℝ := fun q => f q * Real.exp (κ * q)
  have hd : ∀ q, HasDerivAt g (deriv f q * Real.exp (κ * q) + f q * (Real.exp (κ * q) * (κ * 1))) q :=
    fun q => (hf q).hasDerivAt.mul (((hasDerivAt_id q).const_mul κ).exp)
  have hg : Differentiable ℝ g := fun q => (hd q).differentiableAt
  have hanti : AntitoneOn g (Set.Icc q0 (1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hg.continuous.continuousOn
      hg.differentiableOn ?_
    intro q hq
    rw [interior_Icc] at hq
    rw [(hd q).deriv]
    have := h q hq.1 hq.2
    have he := Real.exp_pos (κ * q)
    nlinarith
  have h1 := hanti ⟨le_refl q0, hq0⟩ ⟨hq0, le_refl _⟩ hq0
  simp only [g] at h1
  have e1 : Real.exp (κ * (1 / 2)) * Real.exp (-κ * (1 / 2 - q0)) = Real.exp (κ * q0) := by
    rw [← Real.exp_add]; congr 1; ring
  have he := Real.exp_pos (κ * (1 / 2))
  have : f (1 / 2) * Real.exp (κ * (1 / 2)) ≤ f q0 * Real.exp (-κ * (1 / 2 - q0)) * Real.exp (κ * (1 / 2)) := by
    calc f (1 / 2) * Real.exp (κ * (1 / 2)) ≤ f q0 * Real.exp (κ * q0) := h1
      _ = _ := by rw [mul_assoc, mul_comm (Real.exp (-κ * (1 / 2 - q0))), e1]
  exact le_of_mul_le_mul_right this he

theorem g_bound_one (q : ℝ) (hq : 0 ≤ q) :
    q / (1 - q) ^ (1 - 1) + 2 * (1 - q) / q ^ (1 - 1) ≤ 2 := by
  simp
  linarith

theorem final_arith (n N dG dH A : ℝ) (hn : 2 ≤ n) (hnN : n ≤ N) (hA : 0 < A)
    (hdens : dG / Real.log N ≤ dH / Real.log n)
    (hF : Real.log (4 / 3) ≤ Real.log n * Real.exp (-(dH / (A * Real.log n)))) :
    dG ≤ A * Real.log N * (Real.log (Real.log N) + 2) := by
  have hln : 0 < Real.log n := Real.log_pos (by linarith)
  have hlN : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have hlN0 : 0 < Real.log N := lt_of_lt_of_le hln hlN
  have hc : 1 / 4 ≤ Real.log (4 / 3) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 4 / 3) (by norm_num)
    norm_num at this
    linarith
  have hes : Real.exp (dH / (A * Real.log n)) ≤ 4 * Real.log n := by
    have h1 : Real.log (4 / 3) * Real.exp (dH / (A * Real.log n)) ≤ Real.log n := by
      have := mul_le_mul_of_nonneg_right hF (Real.exp_pos (dH / (A * Real.log n))).le
      rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
    nlinarith [Real.exp_pos (dH / (A * Real.log n))]
  have hs : dH / (A * Real.log n) ≤ Real.log (Real.log N) + 2 := by
    have h1 : dH / (A * Real.log n) ≤ Real.log (4 * Real.log n) := by
      rw [← Real.log_exp (dH / (A * Real.log n))]
      exact Real.log_le_log (Real.exp_pos _) hes
    rw [Real.log_mul (by norm_num) hln.ne'] at h1
    have h2 : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have h3 : Real.log (Real.log n) ≤ Real.log (Real.log N) := Real.log_le_log hln hlN
    linarith
  have hdH : dH ≤ A * Real.log n * (Real.log (Real.log N) + 2) := by
    have hpos : 0 < A * Real.log n := by positivity
    exact (div_le_iff₀ hpos).mp hs |>.trans_eq (by ring)
  have h4 : dG ≤ dH / Real.log n * Real.log N := by
    rwa [div_le_iff₀ hlN0] at hdens
  calc dG ≤ dH / Real.log n * Real.log N := h4
    _ ≤ (A * Real.log n * (Real.log (Real.log N) + 2)) / Real.log n * Real.log N := by
        gcongr
    _ = A * Real.log N * (Real.log (Real.log N) + 2) := by
        field_simp

end WeightedRainbowCycle.Dev.EngineAnalysis
end

section
set_option autoImplicit false

namespace WeightedRainbowCycle.Dev.EngineGraph
open WeightedRainbowCycle.Weighted

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [DecidableEq C]

/-- The multigraph on the vertices and edges of a subgraph `H`. -/
noncomputable def subGraph (G : Model V E C) (H : Subgraph G) : Graph ↥H.verts ↥H.edges where
  vertexSet := Set.univ
  IsLink e u v := G.graph.IsLink e.1 u.1 v.1
  edgeSet := Set.univ
  isLink_symm := fun _ _ => ⟨fun _ _ h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h h'
    rcases G.graph.eq_or_eq_of_isLink_of_isLink h h' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  edge_mem_iff_exists_isLink := by
    intro e
    simp only [Set.mem_univ, true_iff]
    obtain ⟨u, v, h⟩ := G.graph.exists_isLink_of_mem_edgeSet (by rw [G.allEdges]; trivial)
    exact ⟨⟨u, H.incident_mem _ e.2 u ⟨v, h⟩⟩, ⟨v, H.incident_mem _ e.2 v ⟨u, h.symm⟩⟩, h⟩
  left_mem_of_isLink := by intros; trivial

/-- The submodel of a subgraph, on subtypes. -/
noncomputable def subModel (G : Model V E C) (H : Subgraph G) : Model ↥H.verts ↥H.edges C where
  graph := subGraph G H
  allVertices := rfl
  allEdges := rfl
  loopless := fun e u h => G.loopless e.1 u.1 h
  weight := fun e => G.weight e.1
  weight_nonneg := fun e => G.weight_nonneg e.1
  colors := fun e => G.colors e.1
  colors_nonempty := fun e => G.colors_nonempty e.1

theorem subModel_inc (G : Model V E C) (H : Subgraph G) (e : ↥H.edges) (u : ↥H.verts) :
    (subModel G H).graph.Inc e u ↔ G.graph.Inc e.1 u.1 := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v.1, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, H.incident_mem _ e.2 v ⟨u.1, hv.symm⟩⟩, hv⟩

theorem subModel_admissible (G : Model V E C) (H : Subgraph G) (ell : ℕ) (delta : ℝ)
    (h : G.Admissible ell delta) : (subModel G H).Admissible ell delta := by
  classical
  refine ⟨fun e => h.1 e.1, fun u c => ?_⟩
  refine le_trans ?_ (h.2 u.1 c)
  unfold Model.colorDegree
  let F : E → ℝ := fun e => if G.graph.Inc e u.1 ∧ c ∈ G.colors e then G.weight e else 0
  have hF : ∀ e, 0 ≤ F e := fun e => by
    simp only [F]; split_ifs
    · exact G.weight_nonneg e
    · exact le_rfl
  have h1 : (∑ e : ↥H.edges, if (subModel G H).graph.Inc e u ∧ c ∈ (subModel G H).colors e then
      (subModel G H).weight e else 0) = ∑ e : ↥H.edges, F e.1 := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    exact if_congr (and_congr (subModel_inc G H e u) Iff.rfl) rfl rfl
  rw [h1, Finset.sum_coe_sort H.edges F]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => hF e)

theorem subModel_cycle (G : Model V E C) (H : Subgraph G)
    (h : HasRainbowCycle (subModel G H)) : HasRainbowCycle G := by
  obtain ⟨n, v, e, hn, ⟨hl, hd⟩, h0, hinj, heinj⟩ := h
  exact ⟨n, fun i => (v i).1, fun i => (e i).1, hn, ⟨fun i => hl i, fun i j hij => hd i j hij⟩,
    congrArg Subtype.val h0, Subtype.val_injective.comp hinj, Subtype.val_injective.comp heinj⟩

theorem subModel_boundaryMass (G : Model V E C) (H : Subgraph G) (S : Finset ↥H.verts) :
    (subModel G H).boundaryMass S =
      H.boundaryMass (S.map (Function.Embedding.subtype _)) := by
  classical
  unfold Model.boundaryMass Subgraph.boundaryMass
  rw [← Finset.sum_coe_sort H.edges]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨u, hu, v, hv, hl⟩
    refine ⟨u.1, Finset.mem_map_of_mem _ hu, v.1, ?_, hl⟩
    intro hh
    rw [Finset.mem_map] at hh
    obtain ⟨v', hv', hvv⟩ := hh
    exact hv (by have := Subtype.ext hvv; rwa [this] at hv')
  · rintro ⟨u, hu, v, hv, hl⟩
    rw [Finset.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have hvH : v ∈ H.verts := H.incident_mem _ e.2 v ⟨u'.1, hl.symm⟩
    refine ⟨u', hu', ⟨v, hvH⟩, ?_, hl⟩
    intro hh
    exact hv (Finset.mem_map.mpr ⟨_, hh, rfl⟩)

/-- Natural-number indexed version of a nonempty closed rainbow walk containing a rainbow cycle. -/
theorem closed_walk_cycle_nat (G : Model V E C) (n : ℕ) (vN : ℕ → V) (eN : ℕ → E)
    (hn : 1 ≤ n)
    (hlink : ∀ k, k < n → G.graph.IsLink (eN k) (vN k) (vN (k + 1)))
    (hdisj : ∀ k l, k < n → l < n → k ≠ l → Disjoint (G.colors (eN k)) (G.colors (eN l)))
    (hclosed : vN 0 = vN n) : HasRainbowCycle G := by
  classical
  have hex : ∃ j, 1 ≤ j ∧ ∃ i, i < j ∧ vN i = vN j := ⟨n, hn, 0, by omega, hclosed⟩
  let j := Nat.find hex
  obtain ⟨hj1, i, hij, hvij⟩ := Nat.find_spec hex
  have hjn : j ≤ n := Nat.find_min' hex ⟨hn, 0, by omega, hclosed⟩
  have hmin : ∀ j', j' < j → ∀ i', i' < j' → vN i' ≠ vN j' := fun j' hj' i' hi' hh => by
    have := Nat.find_min hex hj'
    exact this ⟨by omega, i', hi', hh⟩
  have hm2 : 2 ≤ j - i := by
    by_contra hlt
    have hj : j = i + 1 := by omega
    have hl := hlink i (by omega)
    rw [← hj, ← hvij] at hl
    exact G.loopless _ _ hl
  refine ⟨j - i, fun k => vN (i + k), fun k => eN (i + k), hm2, ⟨fun k => ?_, fun k l hkl => ?_⟩, ?_, ?_, ?_⟩
  · exact hlink (i + k) (by have := k.2; omega)
  · exact hdisj _ _ (by have := k.2; omega) (by have := l.2; omega)
      (fun h => hkl (Fin.ext (by simpa using h)))
  · show vN (i + 0) = vN (i + (j - i))
    rw [Nat.add_zero, Nat.add_sub_cancel' hij.le]; exact hvij
  · intro k l hkl
    simp only at hkl
    by_contra hne
    have hk := k.2
    have hl := l.2
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : k.1 ≠ l.1) with h | h
    · exact hmin (i + l) (by omega) (i + k) (by omega) hkl
    · exact hmin (i + k) (by omega) (i + l) (by omega) hkl.symm
  · intro k l hkl
    by_contra hne
    have hd := hdisj (i + k) (i + l) (by have := k.2; omega) (by have := l.2; omega)
      (fun h => hne (Fin.ext (by omega)))
    simp only at hkl
    rw [hkl] at hd
    exact (G.colors_nonempty _).ne_empty (Finset.disjoint_self_iff_empty _ |>.mp hd)

/-- A reachability witness for `y ≠ x`, as natural-number indexed functions. -/
theorem reach_nat (G : Model V E C) (x y : V) (A : Set C) (hxy : x ≠ y)
    (h : y ∈ G.reachable x A) :
    ∃ (n : ℕ) (vN : ℕ → V) (eN : ℕ → E), 1 ≤ n ∧ vN 0 = x ∧ vN n = y ∧
      (∀ k, k < n → G.graph.IsLink (eN k) (vN k) (vN (k + 1))) ∧
      (∀ k l, k < n → l < n → k ≠ l → Disjoint (G.colors (eN k)) (G.colors (eN l))) ∧
      (∀ k, k < n → ∀ c ∈ G.colors (eN k), c ∈ A) := by
  classical
  unfold Model.reachable at h
  rw [Finset.mem_filter] at h
  obtain ⟨n, v, e, ⟨hl, hd⟩, h0, hlast, hA⟩ := h.2
  have hn : 1 ≤ n := by
    by_contra hlt
    have : n = 0 := by omega
    subst this
    exact hxy (h0.symm.trans hlast)
  let vN : ℕ → V := fun k => v ⟨min k n, by omega⟩
  let eN : ℕ → E := fun k => e ⟨min k (n - 1), by omega⟩
  have hvN : ∀ k (hk : k < n + 1), vN k = v ⟨k, hk⟩ := fun k hk => by
    simp only [vN]; congr 1; exact Fin.ext (by simp; omega)
  have heN : ∀ k (hk : k < n), eN k = e ⟨k, hk⟩ := fun k hk => by
    simp only [eN]; congr 1; exact Fin.ext (by simp; omega)
  refine ⟨n, vN, eN, hn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvN 0 (by omega)]; exact h0
  · rw [hvN n (by omega)]; exact hlast
  · intro k hk
    rw [heN k hk, hvN k (by omega), hvN (k + 1) (by omega)]
    exact hl ⟨k, hk⟩
  · intro k l hk hl' hkl
    rw [heN k hk, heN l hl']
    exact hd ⟨k, hk⟩ ⟨l, hl'⟩ (fun h => hkl (congrArg Fin.val h))
  · intro k hk
    rw [heN k hk]
    exact hA ⟨k, hk⟩

/-- Two rainbow walks from `x` to `y ≠ x` with disjoint color sets give a rainbow cycle. -/
theorem two_walks_cycle (G : Model V E C) (x y : V) (A B : Set C) (hxy : x ≠ y)
    (hAB : Disjoint A B) (hA : y ∈ G.reachable x A) (hB : y ∈ G.reachable x B) :
    HasRainbowCycle G := by
  obtain ⟨p, vP, eP, hp, hP0, hPp, hPl, hPd, hPA⟩ := reach_nat G x y A hxy hA
  obtain ⟨q, vQ, eQ, hq, hQ0, hQq, hQl, hQd, hQB⟩ := reach_nat G x y B hxy hB
  have hcross : ∀ k l, k < p → l < q → Disjoint (G.colors (eP k)) (G.colors (eQ l)) := by
    intro k l hk hl
    rw [Finset.disjoint_left]
    intro c hcP hcQ
    exact Set.disjoint_left.mp hAB (hPA k hk c hcP) (hQB l hl c hcQ)
  let vC : ℕ → V := fun k => if k ≤ p then vP k else vQ (p + q - k)
  let eC : ℕ → E := fun k => if k < p then eP k else eQ (p + q - 1 - k)
  have hvC1 : ∀ k, k ≤ p → vC k = vP k := fun k hk => by simp [vC, hk]
  have hvC2 : ∀ k, p ≤ k → vC k = vQ (p + q - k) := fun k hk => by
    by_cases h : k = p
    · subst h; simp [vC, hPp, ← hQq]
    · simp [vC, show ¬ k ≤ p by omega]
  have heC1 : ∀ k, k < p → eC k = eP k := fun k hk => by simp [eC, hk]
  have heC2 : ∀ k, p ≤ k → eC k = eQ (p + q - 1 - k) := fun k hk => by
    simp [eC, show ¬ k < p by omega]
  refine closed_walk_cycle_nat G (p + q) vC eC (by omega) ?_ ?_ ?_
  · intro k hk
    by_cases h1 : k < p
    · rw [heC1 k h1, hvC1 k h1.le, hvC1 (k + 1) h1]
      exact hPl k h1
    · rw [heC2 k (by omega), hvC2 k (by omega), hvC2 (k + 1) (by omega),
        show p + q - k = (p + q - 1 - k) + 1 by omega, show p + q - (k + 1) = p + q - 1 - k by omega]
      exact (hQl _ (by omega)).symm
  · intro k l hk hl hkl
    by_cases h1 : k < p <;> by_cases h2 : l < p
    · rw [heC1 k h1, heC1 l h2]; exact hPd k l h1 h2 hkl
    · rw [heC1 k h1, heC2 l (by omega)]; exact hcross _ _ h1 (by omega)
    · rw [heC2 k (by omega), heC1 l h2]; exact (hcross _ _ h2 (by omega)).symm
    · rw [heC2 k (by omega), heC2 l (by omega)]; exact hQd _ _ (by omega) (by omega) (by omega)
  · rw [hvC1 0 (by omega), hvC2 (p + q) (by omega), Nat.sub_self, hP0, hQ0]

theorem sampledColors_disjoint (G : Model V E C) (z : {c // c ∈ G.activeColors} → Bool) :
    Disjoint (G.sampledColors z) (G.sampledColors (fun a => !z a)) := by
  rw [Set.disjoint_left]
  rintro c ⟨a, rfl, ha⟩ ⟨a', ha', hz'⟩
  have : a' = a := Subtype.ext ha'
  subst this
  simp_all

/-- Without a rainbow cycle, `|U(A)| + |U(Aᶜ)| ≤ n + 1`. -/
theorem compl_card (G : Model V E C) (hnc : ¬ HasRainbowCycle G) (x : V)
    (z : {c // c ∈ G.activeColors} → Bool) :
    (G.reachable x (G.sampledColors z)).card +
      (G.reachable x (G.sampledColors (fun a => !z a))).card ≤ Fintype.card V + 1 := by
  classical
  have hsub : G.reachable x (G.sampledColors z) ∩ G.reachable x (G.sampledColors (fun a => !z a))
      ⊆ {x} := by
    intro y hy
    rw [Finset.mem_inter] at hy
    by_contra hne
    exact hnc (two_walks_cycle G x y _ _ (fun h => hne (by simp [h]))
      (sampledColors_disjoint G z) hy.1 hy.2)
  have h1 := Finset.card_union_add_card_inter (G.reachable x (G.sampledColors z))
    (G.reachable x (G.sampledColors (fun a => !z a)))
  have h2 := Finset.card_le_univ
    (G.reachable x (G.sampledColors z) ∪ G.reachable x (G.sampledColors (fun a => !z a)))
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_singleton] at h3
  omega

/-- The whole graph as a subgraph. -/
def fullSub (G : Model V E C) : Subgraph G where
  verts := Finset.univ
  edges := Finset.univ
  incident_mem := fun _ _ u _ => Finset.mem_univ u

theorem fullSub_degree (G : Model V E C) : (fullSub G).degree = G.degree := by
  unfold Subgraph.degree Model.degree fullSub
  simp

theorem exists_densityMax (G : Model V E C) (h : 2 ≤ Fintype.card V) :
    ∃ H : Subgraph G, H.IsDensityMax := by
  classical
  let S : Finset (Finset V × Finset E) := Finset.univ.filter
    (fun p => (∀ e ∈ p.2, ∀ u, G.graph.Inc e u → u ∈ p.1) ∧ 2 ≤ p.1.card)
  have hS : S.Nonempty := ⟨(Finset.univ, Finset.univ), by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ _ u _ => by simp, by simpa using h⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S
    (fun p => (2 * (∑ e ∈ p.2, G.weight e) / p.1.card) / Real.log p.1.card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  refine ⟨⟨p.1, p.2, hp.1⟩, hp.2, fun K hK => ?_⟩
  have := hmax (K.verts, K.edges) (by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨K.incident_mem, hK⟩)
  exact this

end WeightedRainbowCycle.Dev.EngineGraph
end

section
set_option autoImplicit false

namespace WeightedRainbowCycle.Dev.Engine
open WeightedRainbowCycle.Weighted WeightedRainbowCycle.Dev.EngineGraph
  WeightedRainbowCycle.Dev.EngineAnalysis DiffNeighbors.Bias

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [DecidableEq C]

theorem mem_reachable_self (G : Model V E C) (x : V) (A : Set C) : x ∈ G.reachable x A := by
  classical
  unfold Model.reachable
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, 0, fun _ => x, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩,
    rfl, rfl, fun i => i.elim0⟩

theorem reach_card_pos (G : Model V E C) (x : V) (A : Set C) : 1 ≤ (G.reachable x A).card :=
  Finset.card_pos.mpr ⟨x, mem_reachable_self G x A⟩

theorem logReach_nonneg (G : Model V E C) (x : V) (z : {c // c ∈ G.activeColors} → Bool) :
    0 ≤ G.logReach x z := by
  unfold Model.logReach
  exact Real.log_nonneg (by exact_mod_cast reach_card_pos G x _)

theorem logReach_le (G : Model V E C) (x : V) (z : {c // c ∈ G.activeColors} → Bool) :
    G.logReach x z ≤ Real.log (Fintype.card V) := by
  unfold Model.logReach
  refine Real.log_le_log (by exact_mod_cast reach_card_pos G x _) ?_
  exact_mod_cast Finset.card_le_univ _

/-- Pointwise form of Lemma 4.1 on the submodel. -/
theorem pointwise_density (G : Model V E C) (H : Subgraph G) (hmax : H.IsDensityMax)
    (x : ↥H.verts) (z : {c // c ∈ (subModel G H).activeColors} → Bool) :
    H.degree / (2 * Real.log H.verts.card) *
        (Real.log H.verts.card - (subModel G H).logReach x z) ≤
      (subModel G H).boundaryRatio x z := by
  classical
  have hUcard : 1 ≤ ((subModel G H).reachable x ((subModel G H).sampledColors z)).card :=
    reach_card_pos _ _ _
  have hS : (((subModel G H).reachable x ((subModel G H).sampledColors z)).map
      (Function.Embedding.subtype _)).Nonempty :=
    ⟨x.1, Finset.mem_map_of_mem _ (mem_reachable_self _ x _)⟩
  have hSH : (((subModel G H).reachable x ((subModel G H).sampledColors z)).map
      (Function.Embedding.subtype _)) ⊆ H.verts := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hv
    exact u.2
  have hde := density_expansion G H hmax _ hS hSH
  have hbm := subModel_boundaryMass G H ((subModel G H).reachable x ((subModel G H).sampledColors z))
  have hnpos : (0 : ℝ) < H.verts.card := by
    have := hmax.1
    exact_mod_cast (by omega : 0 < H.verts.card)
  have hUpos : (0 : ℝ) < ((subModel G H).reachable x ((subModel G H).sampledColors z)).card := by
    exact_mod_cast hUcard
  rw [Finset.card_map, Real.log_div hnpos.ne' hUpos.ne'] at hde
  unfold Model.boundaryRatio Model.logReach
  rw [hbm]
  exact hde

theorem log_pair (a b N : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a + b ≤ N + 1) :
    Real.log a + Real.log b ≤ 2 * Real.log (((N : ℝ) + 1) / 2) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hsum : (a : ℝ) + b ≤ (N : ℝ) + 1 := by exact_mod_cast h
  rw [← Real.log_mul (by linarith) (by linarith), show (2 : ℝ) * Real.log (((N : ℝ) + 1) / 2) =
    Real.log ((((N : ℝ) + 1) / 2) ^ 2) by rw [Real.log_pow]; norm_num]
  refine Real.log_le_log (by positivity) ?_
  nlinarith [sq_nonneg ((a : ℝ) - b)]

theorem lower_bound (G : Model V E C) (hnc : ¬ HasRainbowCycle G) (hN : 2 ≤ Fintype.card V)
    (x : V) :
    Real.log (4 / 3) ≤ Real.log (Fintype.card V) - bernExp (1 / 2) (G.logReach x) := by
  have hNr : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hpt : ∀ z : {c // c ∈ G.activeColors} → Bool,
      G.logReach x z + G.logReach x (fun a => !z a) ≤ 2 * Real.log (((Fintype.card V : ℝ) + 1) / 2) := by
    intro z
    have h1 := compl_card G hnc x z
    have hu := reach_card_pos G x (G.sampledColors z)
    have hu' := reach_card_pos G x (G.sampledColors (fun a => !z a))
    unfold Model.logReach
    exact log_pair _ _ _ hu hu' h1
  have hE : bernExp (1 / 2) (G.logReach x) ≤ Real.log (((Fintype.card V : ℝ) + 1) / 2) := by
    have h1 : bernExp (1 / 2) (fun z => G.logReach x z + G.logReach x (fun a => !z a)) =
        2 * bernExp (1 / 2) (G.logReach x) := by
      rw [bernExp_add, bernExp_compl_half]; ring
    have h2 := bernExp_le (p := 1 / 2) (by norm_num) (by norm_num)
      (a := fun z => G.logReach x z + G.logReach x (fun a => !z a)) _ hpt
    linarith
  have hlog : Real.log (4 / 3) ≤ Real.log (Fintype.card V) - Real.log (((Fintype.card V : ℝ) + 1) / 2) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ (by linarith)]
    linarith
  linarith

theorem engine_main (G : Model V E C) (ell : ℕ) (delta : ℝ) (hell : 1 ≤ ell) (hdelta : 0 < delta)
    (hadm : G.Admissible ell delta) (hN : 2 ≤ Fintype.card V) (q0 M : ℝ)
    (hq0 : 0 < q0) (hq0' : q0 < 1 / 2)
    (hM : ∀ q, q0 ≤ q → q ≤ 1 / 2 → q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1) ≤ M)
    (hnc : ¬ HasRainbowCycle G) :
    G.degree ≤ (2 * delta * M / (1 / 2 - q0)) * Real.log (Fintype.card V) *
      (Real.log (Real.log (Fintype.card V)) + 2) := by
  classical
  obtain ⟨H, hH⟩ := exists_densityMax G hN
  have hn2 : 2 ≤ H.verts.card := hH.1
  have hnN : H.verts.card ≤ Fintype.card V := by simpa using Finset.card_le_univ H.verts
  have hnr : (2 : ℝ) ≤ H.verts.card := by exact_mod_cast hn2
  have hnNr : (H.verts.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hnN
  have hdens : G.degree / Real.log (Fintype.card V) ≤ H.degree / Real.log H.verts.card := by
    have := hH.2 (fullSub G) (by simpa [fullSub] using hN)
    rw [fullSub_degree] at this
    simpa [fullSub] using this
  have hlogn : 0 < Real.log H.verts.card := Real.log_pos (by linarith)
  have hadm' := subModel_admissible G H ell delta hadm
  have hnc' : ¬ HasRainbowCycle (subModel G H) := fun h => hnc (subModel_cycle G H h)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < H.verts.card)
  let x : ↥H.verts := ⟨a, ha⟩
  have hcardW : Fintype.card ↥H.verts = H.verts.card := Fintype.card_coe _
  let F : ℝ → ℝ := fun p => Real.log H.verts.card - bernExp p ((subModel G H).logReach x)
  have hFd : Differentiable ℝ F := (differentiable_const _).sub (bernExp_differentiable _)
  have hlr_le : ∀ z, (subModel G H).logReach x z ≤ Real.log H.verts.card := fun z => by
    have := logReach_le (subModel G H) x z
    rwa [hcardW] at this
  have hFle : ∀ q, 0 ≤ q → q ≤ 1 → F q ≤ Real.log H.verts.card := fun q h0 h1 => by
    simp only [F]
    linarith [bernExp_nonneg h0 h1 (logReach_nonneg (subModel G H) x)]
  have hFnn : ∀ q, 0 ≤ q → q ≤ 1 → 0 ≤ F q := fun q h0 h1 => by
    simp only [F]
    linarith [bernExp_le h0 h1 _ hlr_le]
  have hdegH : 0 ≤ H.degree := by
    unfold Subgraph.degree
    exact div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ => G.weight_nonneg e))
      (Nat.cast_nonneg _)
  have hc1nn : 0 ≤ H.degree / (2 * Real.log H.verts.card) := div_nonneg hdegH (by positivity)
  have hFeq : ∀ q, F q = bernExp q (fun z => Real.log H.verts.card - (subModel G H).logReach x z) :=
    fun q => by rw [bernExp_sub, bernExp_const]
  have hkey : ∀ q, 0 < q → q < 1 → H.degree / (2 * Real.log H.verts.card) * F q ≤
      delta * (q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1)) * (-deriv F q) := by
    intro q hq0 hq1
    have h1 : H.degree / (2 * Real.log H.verts.card) * F q ≤
        bernExp q ((subModel G H).boundaryRatio x) := by
      rw [hFeq, ← bernExp_mul_left]
      exact bernExp_mono hq0.le hq1.le (fun z => pointwise_density G H hH x z)
    have h2 := boundary_derivative (subModel G H) ell hell delta hdelta.le hadm' x q hq0 hq1
    have h3 : deriv F q = - deriv (fun p => bernExp p ((subModel G H).logReach x)) q := by
      simp only [F]
      exact deriv_const_sub _
    rw [h3, neg_neg]
    exact h1.trans h2
  have hgpos : ∀ q : ℝ, 0 < q → q < 1 →
      0 < q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1) := by
    intro q h0 h1
    have h2 : 0 < 1 - q := by linarith
    have h3 := div_pos h0 (pow_pos h2 (ell - 1))
    have h4 := div_pos (mul_pos two_pos h2) (pow_pos h0 (ell - 1))
    linarith
  have hMpos : 0 < M := by
    have h1 := hM (1 / 2) (by linarith) le_rfl
    have h2 := hgpos (1 / 2) (by norm_num) (by norm_num)
    linarith
  have hdM : 0 < delta * M := mul_pos hdelta hMpos
  have hode : ∀ q, q0 < q → q < 1 / 2 →
      deriv F q ≤ -(H.degree / (2 * Real.log H.verts.card) / (delta * M)) * F q := by
    intro q h1 h2
    have hq0 : 0 < q := by linarith
    have hq1 : q < 1 := by linarith
    have hk := hkey q hq0 hq1
    have hFq := hFnn q hq0.le hq1.le
    have hD : 0 ≤ -deriv F q := by
      have : 0 ≤ delta * (q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1)) * (-deriv F q) :=
        le_trans (mul_nonneg hc1nn hFq) hk
      exact (mul_nonneg_iff_of_pos_left (mul_pos hdelta (hgpos q hq0 hq1))).mp this
    have hgM := hM q h1.le h2.le
    have h3 : delta * (q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1)) * (-deriv F q) ≤
        delta * M * (-deriv F q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgM hdelta.le) hD
    have h4 := hk.trans h3
    have h5 : -(H.degree / (2 * Real.log H.verts.card) / (delta * M)) * F q * (delta * M) =
        -(H.degree / (2 * Real.log H.verts.card) * F q) := by
      field_simp
    refine le_of_mul_le_mul_right ?_ hdM
    rw [h5]
    linarith
  have hodeb := ode_bound F hFd (H.degree / (2 * Real.log H.verts.card) / (delta * M)) q0
    hq0'.le hode
  have hupper : F (1 / 2) ≤ Real.log H.verts.card *
      Real.exp (-(H.degree / (2 * Real.log H.verts.card) / (delta * M)) * (1 / 2 - q0)) :=
    hodeb.trans (mul_le_mul_of_nonneg_right (hFle q0 hq0.le (by linarith)) (Real.exp_pos _).le)
  have hlower : Real.log (4 / 3) ≤ F (1 / 2) := by
    have := lower_bound (subModel G H) hnc' (by rw [hcardW]; exact hn2) x
    rwa [hcardW] at this
  have hA : 0 < 2 * delta * M / (1 / 2 - q0) := by
    have : 0 < 1 / 2 - q0 := by linarith
    positivity
  have hexp : -(H.degree / (2 * Real.log H.verts.card) / (delta * M)) * (1 / 2 - q0) =
      -(H.degree / (2 * delta * M / (1 / 2 - q0) * Real.log H.verts.card)) := by
    have : (1 / 2 - q0) ≠ 0 := by linarith
    field_simp
  rw [hexp] at hupper
  exact final_arith (H.verts.card : ℝ) (Fintype.card V : ℝ) G.degree H.degree _ hnr hnNr hA hdens
    (hlower.trans hupper)

end WeightedRainbowCycle.Dev.Engine
end

section
set_option autoImplicit false

namespace WeightedRainbowCycle.Weighted.Supplement

theorem chk_proper_rainbow_cycle :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ (V E C : Type*) [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] [DecidableEq C]
        (G : Model V E C),
        N₀ ≤ Fintype.card V → (∀ e, G.weight e = 1) → G.Admissible 1 1 →
        9 * Real.log (Fintype.card V) * Real.log (Real.log (Fintype.card V)) ≤ G.degree →
        HasRainbowCycle G := by
  refine ⟨⌈Real.exp (Real.exp 161)⌉₊ + 3, by omega, ?_⟩
  intro V E C _ _ _ _ _ G hN _ hadm hdeg
  by_contra hnc
  have hNr : Real.exp (Real.exp 161) < (Fintype.card V : ℝ) := by
    have h1 := Nat.le_ceil (Real.exp (Real.exp 161))
    have h2 : (⌈Real.exp (Real.exp 161)⌉₊ : ℝ) + 3 ≤ (Fintype.card V : ℝ) := by exact_mod_cast hN
    linarith
  have hNpos : (0 : ℝ) < Fintype.card V := lt_trans (Real.exp_pos _) hNr
  have hlogN : Real.exp 161 < Real.log (Fintype.card V) := (Real.lt_log_iff_exp_lt hNpos).mpr hNr
  have hL : 161 < Real.log (Real.log (Fintype.card V)) :=
    (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hlogN)).mpr hlogN
  have hN2 : 2 ≤ Fintype.card V := by omega
  have key := Dev.Engine.engine_main G 1 1 le_rfl one_pos hadm hN2 (1 / 20) 2
    (by norm_num) (by norm_num)
    (fun q h1 h2 => Dev.EngineAnalysis.g_bound_one q (by linarith)) hnc
  have e1 : 2 * (1 : ℝ) * 2 / (1 / 2 - 1 / 20) = 80 / 9 := by norm_num
  rw [e1] at key
  set L := Real.log (Real.log (Fintype.card V))
  have hK : 0 < Real.log (Fintype.card V) := lt_trans (Real.exp_pos _) hlogN
  nlinarith
end WeightedRainbowCycle.Weighted.Supplement
end

theorem solution : type_of% @WeightedRainbowCycle.Weighted.Supplement.chk_proper_rainbow_cycle := @WeightedRainbowCycle.Weighted.Supplement.chk_proper_rainbow_cycle
