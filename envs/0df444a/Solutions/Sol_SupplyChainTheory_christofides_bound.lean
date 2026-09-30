-- Prove2me | solution 1 for SupplyChainTheory.christofides_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:59:10.911718+00:00
-- url     : https://prove2.me/submissions/96b6dfeb-c630-469a-bb3c-aee6cbd7ce47

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp
import Theorems.Thm_SupplyChainTheory_mst_lower_bound

open Classical SupplyChainTheory

private lemma rot_eq {m : ℕ} (k : Fin (m + 1)) : finRotate (m + 1) k = k + 1 := finRotate_apply k

private lemma rot_castSucc {m : ℕ} (i : Fin m) : finRotate (m + 1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

/-- A tour is its Hamiltonian path plus the closing edge. -/
private lemma tourLength_eq_path {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (τ : Equiv.Perm (Fin (m + 1))) :
    tourLength c τ = ∑ i : Fin m, c (τ i.castSucc) (τ i.succ) + c (τ (Fin.last m)) (τ 0) := by
  rw [tourLength, Fin.sum_univ_castSucc, finRotate_last]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rot_castSucc]

/-- `z*` is the length of some tour. -/
private lemma exists_opt_tour {n : ℕ} (c : Fin n → Fin n → ℝ) :
    ∃ τ : Equiv.Perm (Fin n), tourLength c τ = optTourLength c := by
  obtain ⟨τ, hτ⟩ := (Set.range_nonempty (tourLength c)).csInf_mem (Set.finite_range _)
  exact ⟨τ, hτ⟩

/-! ### Chains of triangle inequalities -/

/-- One segment: `c(h a, h b) ≤ ∑_{a ≤ i < b} c(h i, h (i+1))`. -/
private lemma segment_le {α : Type*} (c : α → α → ℝ) (hrefl : ∀ x, c x x = 0)
    (htri : ∀ x y z, c x z ≤ c x y + c y z) (h : ℕ → α) (a : ℕ) :
    ∀ b, a ≤ b → c (h a) (h b) ≤ ∑ i ∈ Finset.Ico a b, c (h i) (h (i + 1)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp [hrefl]
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    linarith [htri (h a) (h b) (h (b + 1))]

private lemma mono_chain (q : ℕ → ℕ) (K : ℕ) (hq : ∀ j < K, q j ≤ q (j + 1)) : q 0 ≤ q K := by
  induction K with
  | zero => exact le_refl _
  | succ K ih => exact (ih (fun j hj => hq j (by omega))).trans (hq K (by omega))

/-- Visiting the points `h (q 0), h (q 1), …, h (q K)` directly is no longer than following
`h` step by step from `q 0` to `q K`. -/
private lemma chain_le {α : Type*} (c : α → α → ℝ) (hrefl : ∀ x, c x x = 0)
    (htri : ∀ x y z, c x z ≤ c x y + c y z) (h : ℕ → α) (q : ℕ → ℕ) (K : ℕ)
    (hq : ∀ j < K, q j ≤ q (j + 1)) :
    ∑ j ∈ Finset.range K, c (h (q j)) (h (q (j + 1)))
      ≤ ∑ i ∈ Finset.Ico (q 0) (q K), c (h i) (h (i + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← Finset.sum_Ico_consecutive _
      (mono_chain q K (fun j hj => hq j (by omega))) (hq K (by omega))]
    have := segment_le c hrefl htri h (q K) (q (K + 1)) (hq K (by omega))
    linarith [ih (fun j hj => hq j (by omega))]
/-! ### Shortcutting a closed walk does not lengthen it -/

/-- The length of a walk, `∑ᵢ c(wᵢ, wᵢ₊₁)`. -/
private noncomputable def walkLen {V : Type*} {G : SimpleGraph V} (c : V → V → ℝ) {u v : V}
    (W : G.Walk u v) : ℝ :=
  ∑ i ∈ Finset.range W.length, c (W.getVert i) (W.getVert (i + 1))

/-- Under symmetric distances the length of a walk is the total cost of its edge list. -/
private lemma walkLen_eq_edges {n : ℕ} {G : SimpleGraph (Fin n)} (c : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, c i j = c j i) {u v : Fin n} (W : G.Walk u v) :
    walkLen c W = (W.edges.map (edgeCost c)).sum := by
  induction W with
  | nil => simp [walkLen]
  | cons h p ih =>
    rw [walkLen, SimpleGraph.Walk.length_cons, Finset.sum_range_succ', SimpleGraph.Walk.edges_cons,
      List.map_cons, List.sum_cons, ← ih, walkLen]
    simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero, edgeCost,
      Sym2.lift_mk]
    rename_i x y z
    rw [hsymm y x]; ring

/-- **Shortcutting.** If `τ` visits the nodes in order of first appearance along a closed walk
through every node, the tour `τ` is no longer than the walk. -/
private lemma shortcut_le {m : ℕ} {G : SimpleGraph (Fin (m + 1))} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hc : IsMetric c) {v : Fin (m + 1)} (W : G.Walk v v) (τ : Equiv.Perm (Fin (m + 1)))
    (hτ : IsShortcut W.support τ) : tourLength c τ ≤ walkLen c W := by
  obtain ⟨hall, hord⟩ := hτ
  set L := W.length with hL
  set g : ℕ → Fin (m + 1) := fun i => W.getVert i with hg
  -- First-appearance positions of the tour nodes along the walk.
  set p : Fin (m + 1) → ℕ := fun k => W.support.idxOf (τ k) with hp
  have hp_le : ∀ k, p k ≤ L := by
    intro k
    show W.support.idxOf (τ k) ≤ W.length
    have := List.idxOf_lt_length_of_mem (hall (τ k))
    rw [SimpleGraph.Walk.length_support] at this
    omega
  have hgp : ∀ k, g (p k) = τ k := by
    intro k
    simp only [hg, hp]
    rw [SimpleGraph.Walk.getVert_eq_support_getElem _ (hp_le k), List.getElem_idxOf]
  -- The tour starts at the start of the walk.
  have hidx0 : W.support.idxOf v = 0 := by
    cases W with
    | nil => simp
    | cons h q => simp [SimpleGraph.Walk.support_cons]
  have hτ0 : τ 0 = v := by
    by_contra hne
    have h1 : τ.symm (τ 0) < τ.symm v := by
      rw [Equiv.symm_apply_apply]
      exact lt_of_le_of_ne (Fin.zero_le _) (fun h => hne (by rw [h, Equiv.apply_symm_apply]))
    have := (hord _ _).mp h1
    rw [hidx0] at this; omega
  have hp0 : p 0 = 0 := by simp only [hp, hτ0, hidx0]
  -- Positions strictly increase along the tour.
  have hpmono : ∀ i : Fin m, p i.castSucc < p i.succ := by
    intro i
    apply (hord _ _).mp
    simp only [Equiv.symm_apply_apply]
    exact Fin.castSucc_lt_succ
  -- The chain of visited positions `p 0, …, p m`, closed off by the walk's end `L`.
  set q : ℕ → ℕ := fun j => if h : j < m + 1 then p ⟨j, h⟩ else L with hq
  have hqmono : ∀ j < m + 1, q j ≤ q (j + 1) := by
    intro j hj
    simp only [hq, dif_pos hj]
    by_cases hj' : j + 1 < m + 1
    · rw [dif_pos hj']
      exact (hpmono ⟨j, by omega⟩).le
    · rw [dif_neg hj']; exact hp_le _
  have hchain := chain_le c hc.refl (fun x y z => hc.triangle x z y) g q (m + 1) hqmono
  have hq0 : q 0 = 0 := by simp [hq, hp0]
  have hqlast : q (m + 1) = L := by simp [hq]
  rw [hq0, hqlast] at hchain
  -- The chain is exactly the tour.
  have htour : tourLength c τ = ∑ j ∈ Finset.range (m + 1), c (g (q j)) (g (q (j + 1))) := by
    rw [tourLength_eq_path, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hq, dif_pos (show (i : ℕ) < m + 1 by omega),
        dif_pos (show (i : ℕ) + 1 < m + 1 by omega), hgp]
      rfl
    · have e1 : q m = p (Fin.last m) := by simp only [hq, dif_pos (show m < m + 1 by omega)]; rfl
      rw [e1, hqlast, hgp, hτ0]
      simp only [hg, hL, SimpleGraph.Walk.getVert_length]
  rw [htour]
  rw [walkLen]
  rw [← Finset.range_eq_Ico] at hchain
  exact hchain
/-! ### Perfect matchings from fixed-point-free involutions -/

/-- The matching `{o j, o (π j)}` on the nodes `o 0, …, o (K-1)`. -/
private def matchOf {n K : ℕ} (o : Fin K → Fin n) (π : Fin K → Fin K) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (fun j => s(o j, o (π j)))

private lemma matchOf_mem_iff {n K : ℕ} (o : Fin K → Fin n) (ho : Function.Injective o)
    (π : Fin K → Fin K) (hinv : ∀ j, π (π j) = j) (a j : Fin K) :
    s(o a, o (π a)) = s(o j, o (π j)) ↔ a = j ∨ a = π j := by
  rw [Sym2.eq_iff, ho.eq_iff, ho.eq_iff, ho.eq_iff, ho.eq_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, hinv j⟩

private lemma matchOf_perfect {n K : ℕ} (o : Fin K → Fin n) (ho : Function.Injective o)
    (π : Fin K → Fin K) (hinv : ∀ j, π (π j) = j) (hfix : ∀ j, π j ≠ j) :
    IsPerfectMatchingOn (Finset.univ.image o) (matchOf o π) := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [matchOf, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨j, rfl⟩ := he
    refine ⟨?_, ?_⟩
    · rw [Sym2.mk_isDiag_iff]
      exact fun h => hfix j (ho h).symm
    · intro v hv
      rw [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl <;> simp
  · intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨j, rfl⟩ := hv
    refine ⟨s(o j, o (π j)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j), Sym2.mem_mk_left _ _⟩, ?_⟩
    rintro e ⟨he, hje⟩
    simp only [matchOf, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨a, rfl⟩ := he
    rw [Sym2.mem_iff, ho.eq_iff, ho.eq_iff] at hje
    exact (matchOf_mem_iff o ho π hinv a j).mpr (by
      rcases hje with rfl | h
      · exact Or.inl rfl
      · right; rw [h, hinv])

/-- Every edge of `matchOf o π` is counted twice, once from each end. -/
private lemma two_mul_matchOf_weight {n K : ℕ} (c : Fin n → Fin n → ℝ) (hsymm : ∀ i j, c i j = c j i)
    (o : Fin K → Fin n) (ho : Function.Injective o) (π : Fin K → Fin K)
    (hinv : ∀ j, π (π j) = j) (hfix : ∀ j, π j ≠ j) :
    2 * edgeSetWeight c (matchOf o π) = ∑ j, c (o j) (o (π j)) := by
  have hcost : ∀ j, edgeCost c s(o j, o (π j)) = c (o j) (o (π j)) := by
    intro j; simp only [edgeCost, Sym2.lift_mk]; rw [hsymm (o (π j))]; ring
  rw [← Finset.sum_congr rfl (fun j _ => hcost j)]
  rw [Finset.sum_comp (fun e => edgeCost c e) (fun j => s(o j, o (π j)))]
  rw [edgeSetWeight, matchOf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
  obtain ⟨j, rfl⟩ := he
  have hfib : Finset.univ.filter (fun a => s(o a, o (π a)) = s(o j, o (π j))) = {j, π j} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact matchOf_mem_iff o ho π hinv a j
  rw [hfib, Finset.card_pair (hfix j).symm, nsmul_eq_mul]
  norm_num
/-! ### The optimal tour shortcut to an even node set splits into two matchings -/

/-- Cyclic successor and predecessor on `Fin K`. -/
private def succC {K : ℕ} (hK : 0 < K) (j : Fin K) : Fin K :=
  ⟨if j.val + 1 = K then 0 else j.val + 1, by split_ifs <;> omega⟩

private def predC {K : ℕ} (hK : 0 < K) (j : Fin K) : Fin K :=
  ⟨if j.val = 0 then K - 1 else j.val - 1, by split_ifs <;> omega⟩

/-- The two alternating pairings of a cycle of even length `K = 2k`. -/
private def pair1 {k : ℕ} (_hk : 0 < k) (j : Fin (2 * k)) : Fin (2 * k) :=
  ⟨if j.val % 2 = 0 then j.val + 1 else j.val - 1, by have := j.isLt; split_ifs <;> omega⟩

private def pair2 {k : ℕ} (hk : 0 < k) (j : Fin (2 * k)) : Fin (2 * k) :=
  ⟨if j.val % 2 = 0 then (if j.val = 0 then 2 * k - 1 else j.val - 1)
    else (if j.val + 1 = 2 * k then 0 else j.val + 1), by have := j.isLt; split_ifs <;> omega⟩

private lemma pair1_inv {k : ℕ} (hk : 0 < k) (j : Fin (2 * k)) : pair1 hk (pair1 hk j) = j := by
  ext; simp only [pair1]; have := j.isLt; split_ifs <;> omega

private lemma pair1_ne {k : ℕ} (hk : 0 < k) (j : Fin (2 * k)) : pair1 hk j ≠ j := by
  intro h; have := congrArg Fin.val h; simp only [pair1] at this; split_ifs at this <;> omega

private lemma pair2_inv {k : ℕ} (hk : 0 < k) (j : Fin (2 * k)) : pair2 hk (pair2 hk j) = j := by
  ext; simp only [pair2, Fin.val_mk]; have := j.isLt
  by_cases h1 : j.val % 2 = 0 <;> by_cases h2 : j.val = 0 <;> by_cases h3 : j.val + 1 = 2 * k <;>
    simp only [h1, h2, h3, if_true, if_false] <;> (try split_ifs) <;> first | omega | contradiction

private lemma pair2_ne {k : ℕ} (hk : 0 < k) (j : Fin (2 * k)) : pair2 hk j ≠ j := by
  intro h; have := congrArg Fin.val h; simp only [pair2] at this
  split_ifs at this <;> omega

private lemma predC_succC {K : ℕ} (hK : 0 < K) (j : Fin K) : predC hK (succC hK j) = j := by
  ext; simp only [predC, succC]; have := j.isLt; split_ifs <;> simp_all <;> omega

private lemma succC_predC {K : ℕ} (hK : 0 < K) (j : Fin K) : succC hK (predC hK j) = j := by
  ext; simp only [predC, succC]; have := j.isLt; split_ifs <;> simp_all <;> omega

/-- The two pairings together use each cycle edge twice (once from each end). -/
private lemma pair_sum {n k : ℕ} (hk : 0 < k) (hK : 0 < 2 * k) (c : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, c i j = c j i) (o : Fin (2 * k) → Fin n) :
    ∑ j, c (o j) (o (pair1 hk j)) + ∑ j, c (o j) (o (pair2 hk j))
      = 2 * ∑ j, c (o j) (o (succC hK j)) := by
  rw [← Finset.sum_add_distrib]
  have hper : ∀ j, c (o j) (o (pair1 hk j)) + c (o j) (o (pair2 hk j))
      = c (o j) (o (succC hK j)) + c (o j) (o (predC hK j)) := by
    intro j
    have e1 : j.val % 2 = 0 → pair1 hk j = succC hK j := by
      intro h; ext; simp only [pair1, succC, if_pos h]; have := j.isLt; split_ifs <;> omega
    have e2 : j.val % 2 ≠ 0 → pair1 hk j = predC hK j := by
      intro h; ext; simp only [pair1, predC, if_neg h]; split_ifs <;> omega
    have e3 : j.val % 2 = 0 → pair2 hk j = predC hK j := by
      intro h; ext; simp only [pair2, predC, if_pos h]
    have e4 : j.val % 2 ≠ 0 → pair2 hk j = succC hK j := by
      intro h; ext; simp only [pair2, succC, if_neg h]
    by_cases h : j.val % 2 = 0
    · rw [e1 h, e3 h]
    · rw [e2 h, e4 h]; ring
  rw [Finset.sum_congr rfl (fun j _ => hper j), Finset.sum_add_distrib]
  suffices hpred : ∑ j, c (o j) (o (predC hK j)) = ∑ j, c (o j) (o (succC hK j)) by
    rw [hpred]; ring
  -- Reindex the predecessor sum by the successor bijection.
  let e : Fin (2 * k) ≃ Fin (2 * k) :=
    ⟨succC hK, predC hK, predC_succC hK, succC_predC hK⟩
  have := Equiv.sum_comp e (fun j => c (o j) (o (predC hK j)))
  simp only [e, Equiv.coe_fn_mk, predC_succC] at this
  rw [← this]
  exact Finset.sum_congr rfl (fun j _ => hsymm _ _)

/-- A periodic sum over any window of one period is the sum over `[0, N)`. -/
private lemma sum_Ico_period (f : ℕ → ℝ) (N : ℕ) (hf : ∀ i, f (i + N) = f i) :
    ∀ a, ∑ i ∈ Finset.Ico a (a + N), f i = ∑ i ∈ Finset.range N, f i := by
  intro a
  induction a with
  | zero => rw [Nat.zero_add, Finset.range_eq_Ico]
  | succ a ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty, Finset.range_zero]
    rw [← ih, Finset.sum_eq_sum_Ico_succ_bot (by omega : a < a + N),
      show a + 1 + N = a + N + 1 by omega, Finset.sum_Ico_succ_top (by omega : a + 1 ≤ a + N), hf]
    ring

/-- **Matching bound.** A minimum perfect matching on an even node set costs at most `z*/2`. -/
private lemma two_mul_minMatching_le {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (hc : IsMetric c)
    (O : Finset (Fin (m + 1))) (hO : Even O.card) (M : Finset (Sym2 (Fin (m + 1))))
    (hM : IsMinMatchingOn c O M) : 2 * edgeSetWeight c M ≤ optTourLength c := by
  obtain ⟨τ, hτ⟩ := exists_opt_tour c
  have hz : 0 ≤ optTourLength c := by
    rw [← hτ]; exact Finset.sum_nonneg (fun k _ => hc.nonneg _ _)
  obtain ⟨k, hk⟩ := hO
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · -- No odd nodes: the empty matching is perfect, so `M` weighs at most `0`.
    have hO0 : O = ∅ := Finset.card_eq_zero.mp (by omega)
    have hempty : IsPerfectMatchingOn O (∅ : Finset (Sym2 (Fin (m + 1)))) := by
      refine ⟨fun e he => absurd he (Finset.notMem_empty e), fun v hv => ?_⟩
      rw [hO0] at hv; exact absurd hv (Finset.notMem_empty v)
    have := hM.2 ∅ hempty
    have h0 : edgeSetWeight c (∅ : Finset (Sym2 (Fin (m + 1)))) = 0 := by simp [edgeSetWeight]
    linarith
  -- List the odd nodes in the order the optimal tour visits them.
  set P := O.image τ.symm with hP
  have hPcard : P.card = 2 * k := by
    rw [hP, Finset.card_image_of_injective _ τ.symm.injective]; omega
  set e := P.orderEmbOfFin hPcard with he
  set o : Fin (2 * k) → Fin (m + 1) := fun j => τ (e j) with ho
  have hoinj : Function.Injective o := fun a b h => e.injective (τ.injective h)
  have hoimg : Finset.univ.image o = O := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, ho]
    constructor
    · rintro ⟨j, rfl⟩
      have hmem : e j ∈ P := P.orderEmbOfFin_mem hPcard j
      rw [hP, Finset.mem_image] at hmem
      obtain ⟨y, hy, hye⟩ := hmem
      rw [← hye, Equiv.apply_symm_apply]; exact hy
    · intro hx
      have : τ.symm x ∈ Set.range e := by
        rw [he, Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem _ hx
      obtain ⟨j, hj⟩ := this
      exact ⟨j, by rw [hj, Equiv.apply_symm_apply]⟩
  have hK : 0 < 2 * k := by omega
  -- The cycle through the odd nodes, in tour order, is no longer than the tour.
  have hcycle : ∑ j, c (o j) (o (succC hK j)) ≤ optTourLength c := by
    set h : ℕ → Fin (m + 1) := fun i => τ ⟨i % (m + 1), Nat.mod_lt _ (by omega)⟩ with hh
    set q : ℕ → ℕ := fun j => if hj : j < 2 * k then (e ⟨j, hj⟩).val else (e ⟨0, hK⟩).val + (m + 1)
      with hq
    have hqmono : ∀ j < 2 * k, q j ≤ q (j + 1) := by
      intro j hj
      simp only [hq, dif_pos hj]
      by_cases hj' : j + 1 < 2 * k
      · rw [dif_pos hj']
        exact (e.strictMono (show (⟨j, hj⟩ : Fin (2 * k)) < ⟨j + 1, hj'⟩ from
          Fin.mk_lt_mk.mpr (by omega))).le
      · rw [dif_neg hj']; have := (e ⟨j, hj⟩).isLt; omega
    have hchain := chain_le c hc.refl (fun x y z => hc.triangle x z y) h q (2 * k) hqmono
    have hq0 : q 0 = (e ⟨0, hK⟩).val := by simp only [hq, dif_pos hK]
    have hqK : q (2 * k) = (e ⟨0, hK⟩).val + (m + 1) := by
      simp only [hq, dif_neg (lt_irrefl (2 * k))]
    rw [hq0, hqK, sum_Ico_period (fun i => c (h i) (h (i + 1))) (m + 1) (by
      intro i; simp only [hh, Nat.add_mod_right, show i + (m + 1) + 1 = i + 1 + (m + 1) by omega])]
      at hchain
    have htour : ∑ i ∈ Finset.range (m + 1), c (h i) (h (i + 1)) = tourLength c τ := by
      rw [tourLength, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hh, rot_eq]
      congr 2
      · ext; simp [Nat.mod_eq_of_lt i.isLt]
      · ext; simp [Fin.val_add, Nat.add_mod_mod]
    have hleft : ∑ j ∈ Finset.range (2 * k), c (h (q j)) (h (q (j + 1)))
        = ∑ j, c (o j) (o (succC hK j)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => c (h (q j)) (h (q (j + 1))))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hj := j.isLt
      have hqj : h (q j) = o j := by
        simp only [hh, hq, dif_pos hj, ho]
        congr 1; ext; simp [Nat.mod_eq_of_lt (e j).isLt]
      have hqs : h (q (j + 1)) = o (succC hK j) := by
        by_cases hj' : j.val + 1 = 2 * k
        · have hs : succC hK j = ⟨0, hK⟩ := by ext; simp [succC, hj']
          rw [hs]
          simp only [hh, hq, ho, dif_neg (show ¬ (j.val + 1 < 2 * k) by omega)]
          congr 1; ext
          simp [Nat.add_mod_right, Nat.mod_eq_of_lt (e _).isLt]
        · have hs : succC hK j = ⟨j.val + 1, by omega⟩ := by ext; simp [succC, hj']
          rw [hs]
          simp only [hh, hq, ho, dif_pos (show j.val + 1 < 2 * k by omega)]
          congr 1; ext
          simp [Nat.mod_eq_of_lt (e _).isLt]
      rw [hqj, hqs]
    rw [← hleft, ← hτ, ← htour]
    exact hchain
  -- Both alternating matchings are perfect on `O`, so `M` is no heavier than either.
  have h1 := hM.2 _ (hoimg ▸ matchOf_perfect o hoinj (pair1 hkpos) (pair1_inv hkpos) (pair1_ne hkpos))
  have h2 := hM.2 _ (hoimg ▸ matchOf_perfect o hoinj (pair2 hkpos) (pair2_inv hkpos) (pair2_ne hkpos))
  have w1 := two_mul_matchOf_weight c hc.symm o hoinj (pair1 hkpos) (pair1_inv hkpos) (pair1_ne hkpos)
  have w2 := two_mul_matchOf_weight c hc.symm o hoinj (pair2 hkpos) (pair2_inv hkpos) (pair2_ne hkpos)
  have hsum := pair_sum hkpos hK c hc.symm o
  linarith

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) (M : Finset (Sym2 (Fin n)))
    (hM : IsMinMatchingOn c (oddNodes T) M) (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v)
    (hW : (W.edges : Multiset (Sym2 (Fin n))) = T.edgeFinset.val + M.val)
    (τ : Equiv.Perm (Fin n)) (hτ : IsShortcut W.support τ) :
    tourLength c τ ≤ (3 / 2 : ℝ) * optTourLength c := by
  -- Lemma 10.9: the tree is no longer than an optimal tour.
  have hmst := mst_lower_bound c hc hn T hT
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Handshaking: there is an even number of odd-degree nodes, so the matching bound applies.
  have hO : Even (oddNodes T).card := by
    rw [oddNodes]; convert T.even_card_odd_degree_vertices
  have hmatch := two_mul_minMatching_le c hc (oddNodes T) hO M hM
  -- The Eulerian walk of `T* + M` has length `z(T*) + z(M)`.
  have hwalk : walkLen c W = graphWeight c T + edgeSetWeight c M := by
    rw [walkLen_eq_edges c hc.symm]
    have : (W.edges.map (edgeCost c)).sum = ((W.edges : Multiset (Sym2 (Fin (m + 1)))).map (edgeCost c)).sum := by
      simp
    rw [this, hW, Multiset.map_add, Multiset.sum_add]
    rfl
  -- Shortcutting does not lengthen the walk.
  have := shortcut_le c hc W τ hτ
  linarith
