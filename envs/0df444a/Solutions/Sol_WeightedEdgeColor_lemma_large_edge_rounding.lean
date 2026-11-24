-- Prove2me | solution 1 for WeightedEdgeColor.lemma_large_edge_rounding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T07:20:15.131133+00:00
-- url     : https://prove2.me/submissions/bedba2a9-08ed-4d54-8adc-03dff10fca35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Theorems.Thm_WeightedEdgeColor_proposition_A_5

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0

namespace WECLRAux

/-- Counting the indices of a multiset family given by multiplicities. -/
theorem card_filter_sigma_sum {T₁ T₂ : Type} [Fintype T₁] [Fintype T₂]
    (M₁ : T₁ → ℕ) (M₂ : T₂ → ℕ) (P : (Σ t, Fin (M₁ t)) ⊕ (Σ t, Fin (M₂ t)) → Prop) [DecidablePred P]
    (P₁ : T₁ → Prop) (P₂ : T₂ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (h₁ : ∀ t m, P (Sum.inl ⟨t, m⟩) ↔ P₁ t) (h₂ : ∀ t m, P (Sum.inr ⟨t, m⟩) ↔ P₂ t) :
    ((Finset.univ : Finset ((Σ t, Fin (M₁ t)) ⊕ (Σ t, Fin (M₂ t)))).filter P).card
      = ∑ t, (if P₁ t then M₁ t else 0) + ∑ t, (if P₂ t then M₂ t else 0) := by
  rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  congr 1
  · apply Finset.sum_congr rfl; intro t _
    by_cases h : P₁ t
    · simp [(h₁ t _).mpr h, h]
    · simp [fun m => (h₁ t m).not.mpr h, h]
  · apply Finset.sum_congr rfl; intro t _
    by_cases h : P₂ t
    · simp [(h₂ t _).mpr h, h]
    · simp [fun m => (h₂ t m).not.mpr h, h]

/-- `c * n ^ p ≤ n ^ q` eventually when `p < q`. -/
theorem rpow_dominate (c p q : ℝ) (hc : 0 < c) (hpq : p < q) (n : ℝ) (hn1 : 1 ≤ n)
    (hn : c ^ (1 / (q - p)) ≤ n) : c * n ^ p ≤ n ^ q := by
  have hn0 : 0 < n := by linarith
  have hqp : 0 < q - p := by linarith
  have h1 : c ≤ n ^ (q - p) := by
    have := Real.rpow_le_rpow (by positivity) hn hqp.le
    rwa [← Real.rpow_mul hc.le, one_div_mul_cancel hqp.ne', Real.rpow_one] at this
  have h2 : n ^ q = n ^ (q - p) * n ^ p := by
    rw [← Real.rpow_add hn0]; ring_nf
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

end WECLRAux

open WeightedEdgeColor WeightedEdgeColor.WGraph WECLRAux

theorem solution (C₁ σ β Cm ε : ℝ) (Ks : ℕ)
    (hC₁ : 0 < C₁) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hCm : 0 < Cm) (hε : 0 < ε) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (b : V → 𝒞 → Fin Ks → ℝ) (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ),
      (∀ e c i j, 0 ≤ XL e c i j) →
      (∀ e c i j, XL e c i j ≠ 0 → β ≤ G.w e ∧ G.w e ≤ b (src e) c i ∧ G.w e ≤ b (tgt e) c j) →
      (∀ e, ∑ c, ∑ i, ∑ j, XL e c i j ≤ 1) →
      (∀ e c, ∑ i, ∑ j, XL e c i j ≤ Cm / n) →
      (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
         + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ) →
      ∃ ψ : E → Option (𝒞 × Fin Ks × Fin Ks),
        (∀ e c i j, ψ e = some (c, i, j) → 0 < XL e c i j) ∧
        (∀ (e e' : E) (v : V) (c : 𝒞) (i : Fin Ks),
          (∃ j, (src e = v ∧ ψ e = some (c, i, j)) ∨ (tgt e = v ∧ ψ e = some (c, j, i))) →
          (∃ j, (src e' = v ∧ ψ e' = some (c, i, j)) ∨ (tgt e' = v ∧ ψ e' = some (c, j, i))) →
          e = e') ∧
        ∀ v, ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e ∧ ψ e = none), G.w e ≤
          ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e),
            G.w e * (1 - ∑ c, ∑ i, ∑ j, XL e c i j) + ε * n + K * n ^ (2 / 3 : ℝ) := by
  classical
  -- fixed constants
  set lam : ℝ := min ε 1 / 8 with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam8 : lam ≤ 1 / 8 := by rw [hlam]; have := min_le_right ε 1; linarith
  have hlamε : lam ≤ ε / 8 := by rw [hlam]; have := min_le_left ε 1; linarith
  set η : ℝ := min σ lam with hη
  have hη0 : 0 < η := lt_min hσ0 hlam0
  have hησ : η ≤ σ := min_le_left _ _
  have hηlam : η ≤ lam := min_le_right _ _
  set Hm : ℕ := ⌊(1 - β) / (lam * β)⌋₊ with hHm
  set uMax : ℝ := β + (Hm + 1) * lam * β with huMax
  obtain ⟨a, ha0, D₀, hA5⟩ := proposition_A_5 (1 / 10) (by norm_num)
  set cB : ℝ := 2 / β + 4 with hcB
  set cL : ℝ := C₁ * (Ks : ℝ) ^ 2 + cB ^ 2 with hcL
  set n₀ : ℝ := max (max 1 (2 * D₀)) (max (2 * (4 / η) ^ (1 / a))
    (max (4 * cL / η) ((4 * (Cm + 2)) ^ (1 / (2 / 3 - 3 / 5 : ℝ))))) with hn₀
  refine ⟨n₀, 3 * (Hm + 1) * uMax, ?_⟩
  intro V E _ _ _ _ G hG src tgt hst n hn hW 𝒞 _ _ hcard b XL hXL0 hXLc hsum hmass hslot
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnD : 2 * D₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hna : 2 * (4 / η) ^ (1 / a) ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnL : 4 * cL / η ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have hnC : (4 * (Cm + 2)) ^ (1 / (2 / 3 - 3 / 5 : ℝ)) ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have hn0 : 0 < n := by linarith
  -- endpoints
  have hmem : ∀ e v, v ∈ G.ends e ↔ v = src e ∨ v = tgt e := by
    intro e v; rw [hst e, Sym2.mem_iff]
  have hst_ne : ∀ e, src e ≠ tgt e := by
    intro e h
    have := G.loopless e
    rw [hst e, Sym2.mk_isDiag_iff] at this
    exact this h
  -- scale parameters
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈n⌉₊ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = m ^ 6 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = ⌈n ^ (2 / 3 : ℝ)⌉₊ := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by
    rw [hT, Nat.one_le_ceil_iff]; positivity
  have hTn : n ^ (2 / 3 : ℝ) ≤ T := by rw [hT]; exact Nat.le_ceil _
  -- large edges, fractions, weight intervals
  let lg : E → Prop := fun e => β ≤ G.w e
  obtain ⟨sE, hsEdef⟩ : ∃ f : E → ℝ, ∀ e, f e = ∑ c, ∑ i, ∑ j, XL e c i j := ⟨_, fun _ => rfl⟩
  obtain ⟨rE, hrEdef⟩ : ∃ f : E → ℝ, ∀ e, f e = 1 - sE e := ⟨_, fun _ => rfl⟩
  have hsE0 : ∀ e, 0 ≤ sE e := fun e => by
    rw [hsEdef]
    exact Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => hXL0 e c i j)))
  have hrE0 : ∀ e, 0 ≤ rE e := fun e => by rw [hrEdef]; have := hsum e; rw [← hsEdef] at this; linarith
  have hrE1 : ∀ e, rE e ≤ 1 := fun e => by rw [hrEdef]; linarith [hsE0 e]
  obtain ⟨hF, hhF⟩ : ∃ f : E → Fin (Hm + 1), ∀ e, (f e : ℕ) = min ⌊(G.w e - β) / (lam * β)⌋₊ Hm :=
    ⟨fun e => ⟨min ⌊(G.w e - β) / (lam * β)⌋₊ Hm, by omega⟩, fun _ => rfl⟩
  obtain ⟨Rvh, hRvh⟩ : ∃ f : V → Fin (Hm + 1) → ℝ,
      ∀ v h, f v h = ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Bvh, hBvh⟩ : ∃ f : V → Fin (Hm + 1) → ℕ, ∀ v h, f v h = ⌈Rvh v h / (1 - lam)⌉₊ + T :=
    ⟨_, fun _ _ => rfl⟩
  have hBpos : ∀ v h, 1 ≤ Bvh v h := fun v h => by rw [hBvh]; omega
  obtain ⟨Bmax, hBlt⟩ : ∃ B : ℕ, ∀ v h, Bvh v h < B := by
    refine ⟨(Finset.univ.sup (fun p : V × Fin (Hm + 1) => Bvh p.1 p.2)) + 1, fun v h => ?_⟩
    have : Bvh v h ≤ Finset.univ.sup (fun p : V × Fin (Hm + 1) => Bvh p.1 p.2) :=
      Finset.le_sup (f := fun p : V × Fin (Hm + 1) => Bvh p.1 p.2) (Finset.mem_univ (v, h))
    exact Nat.lt_succ_of_le this
  -- the instance of Proposition A.5
  let α := E ⊕ (V × 𝒞 × Fin Ks) ⊕ (V × Fin (Hm + 1) × Fin Bmax)
  let job : E → α := fun e => Sum.inl e
  let osl : V → 𝒞 → Fin Ks → α := fun v c i => Sum.inr (Sum.inl (v, c, i))
  let xsl : V → Fin (Hm + 1) → Fin Bmax → α := fun v h k => Sum.inr (Sum.inr (v, h, k))
  obtain ⟨M₁, hM₁⟩ : ∃ f : E × 𝒞 × Fin Ks × Fin Ks → ℕ, ∀ t,
      f t = if lg t.1 then ⌊(N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2⌋₊ else 0 := ⟨_, fun _ => rfl⟩
  let valid₂ : E × Fin Bmax × Fin Bmax → Prop := fun t =>
    lg t.1 ∧ (t.2.1 : ℕ) < Bvh (src t.1) (hF t.1) ∧ (t.2.2 : ℕ) < Bvh (tgt t.1) (hF t.1)
  obtain ⟨M₂, hM₂⟩ : ∃ f : E × Fin Bmax × Fin Bmax → ℕ, ∀ t, f t =
      if valid₂ t then ⌊(N : ℝ) * rE t.1 / ((Bvh (src t.1) (hF t.1) : ℝ) * Bvh (tgt t.1) (hF t.1))⌋₊
      else 0 := ⟨_, fun _ => rfl⟩
  let ι := (Σ t, Fin (M₁ t)) ⊕ (Σ t, Fin (M₂ t))
  let S₁ : E × 𝒞 × Fin Ks × Fin Ks → Finset α := fun t =>
    {job t.1, osl (src t.1) t.2.1 t.2.2.1, osl (tgt t.1) t.2.1 t.2.2.2}
  let S₂ : E × Fin Bmax × Fin Bmax → Finset α := fun t =>
    {job t.1, xsl (src t.1) (hF t.1) t.2.1, xsl (tgt t.1) (hF t.1) t.2.2}
  let S : ι → Finset α := fun i => Sum.elim (fun i => S₁ i.1) (fun i => S₂ i.1) i
  let A : Finset α := (Finset.univ.filter lg).image job
  let isB : α → Prop := fun x => Sum.elim (fun _ => False)
    (Sum.elim (fun _ => True) (fun p : V × Fin (Hm + 1) × Fin Bmax => (p.2.2 : ℕ) < Bvh p.1 p.2.1)) x
  let Bs : Finset α := Finset.univ.filter isB
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (1 - η / 2) * N := ⟨_, rfl⟩
  -- basic membership facts
  have hjobA : ∀ e, job e ∈ A ↔ lg e := by
    intro e
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e', he', h⟩
      have : e' = e := Sum.inl_injective h
      rw [← this]; exact he'
    · intro h; exact ⟨e, h, rfl⟩
  have hAjob : ∀ x ∈ A, ∃ e, lg e ∧ x = job e := by
    intro x hx
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact ⟨e, he, rfl⟩
  have hoslB : ∀ v c i, osl v c i ∈ Bs := by
    intro v c i; simp [Bs, isB, osl]
  have hxslB : ∀ v h k, xsl v h k ∈ Bs ↔ (k : ℕ) < Bvh v h := by
    intro v h k; simp [Bs, isB, xsl]
  have hjobB : ∀ e, job e ∉ Bs := by
    intro e; simp [Bs, isB, job]
  have hM₁pos : ∀ t, 0 < M₁ t → lg t.1 := by
    intro t ht
    by_contra h
    rw [hM₁ t, if_neg h] at ht
    exact lt_irrefl _ ht
  have hM₂pos : ∀ t, 0 < M₂ t → valid₂ t := by
    intro t ht
    by_contra h
    rw [hM₂ t, if_neg h] at ht
    exact lt_irrefl _ ht
  have hdisj : Disjoint A Bs := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨e, -, rfl⟩ := hAjob x hxA
    exact hjobB e hxB
  have hS : ∀ i, S i ⊆ A ∪ Bs ∧ (S i ∩ A).card = 1 ∧ (S i ∩ Bs).card ≤ 2 := by
    intro i
    cases i with
    | inl p =>
      obtain ⟨t, k⟩ := p
      have hlg : lg t.1 := hM₁pos t (Fin.pos k)
      show S₁ t ⊆ A ∪ Bs ∧ (S₁ t ∩ A).card = 1 ∧ (S₁ t ∩ Bs).card ≤ 2
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [S₁, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact Finset.mem_union_left _ ((hjobA _).mpr hlg)
        · exact Finset.mem_union_right _ (hoslB _ _ _)
        · exact Finset.mem_union_right _ (hoslB _ _ _)
      · have : S₁ t ∩ A = {job t.1} := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, hxA⟩
            obtain ⟨e, -, rfl⟩ := hAjob x hxA
            simp only [S₁, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with h | h | h
            · exact h
            · simp [job, osl] at h
            · simp [job, osl] at h
          · rintro rfl
            exact ⟨by simp [S₁], (hjobA _).mpr hlg⟩
        rw [this, Finset.card_singleton]
      · refine le_trans (Finset.card_le_card (t := {osl (src t.1) t.2.1 t.2.2.1,
          osl (tgt t.1) t.2.1 t.2.2.2}) ?_) Finset.card_le_two
        intro x hx
        obtain ⟨hx, hxB⟩ := Finset.mem_inter.mp hx
        simp only [S₁, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact absurd hxB (hjobB _)
        · simp
        · simp
    | inr p =>
      obtain ⟨t, k⟩ := p
      have hv := hM₂pos t (Fin.pos k)
      show S₂ t ⊆ A ∪ Bs ∧ (S₂ t ∩ A).card = 1 ∧ (S₂ t ∩ Bs).card ≤ 2
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [S₂, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact Finset.mem_union_left _ ((hjobA _).mpr hv.1)
        · exact Finset.mem_union_right _ ((hxslB _ _ _).mpr hv.2.1)
        · exact Finset.mem_union_right _ ((hxslB _ _ _).mpr hv.2.2)
      · have : S₂ t ∩ A = {job t.1} := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, hxA⟩
            obtain ⟨e, -, rfl⟩ := hAjob x hxA
            simp only [S₂, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with h | h | h
            · exact h
            · simp [job, xsl] at h
            · simp [job, xsl] at h
          · rintro rfl
            exact ⟨by simp [S₂], (hjobA _).mpr hv.1⟩
        rw [this, Finset.card_singleton]
      · refine le_trans (Finset.card_le_card (t := {xsl (src t.1) (hF t.1) t.2.1,
          xsl (tgt t.1) (hF t.1) t.2.2}) ?_) Finset.card_le_two
        intro x hx
        obtain ⟨hx, hxB⟩ := Finset.mem_inter.mp hx
        simp only [S₂, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact absurd hxB (hjobB _)
        · simp
        · simp
  -- injectivity of the element constructors
  have hjob_inj : ∀ e e', job e = job e' ↔ e = e' := fun e e' => Sum.inl_injective.eq_iff
  have hosl_inj : ∀ v c i v' c' i', osl v c i = osl v' c' i' ↔ v = v' ∧ c = c' ∧ i = i' := by
    intro v c i v' c' i'
    constructor
    · intro h
      have h1 := Sum.inl_injective (Sum.inr_injective h)
      simp only [Prod.mk.injEq] at h1
      exact h1
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  have hxsl_inj : ∀ v h k v' h' k', xsl v h k = xsl v' h' k' ↔ v = v' ∧ h = h' ∧ k = k' := by
    intro v h k v' h' k'
    constructor
    · intro h''
      have h1 := Sum.inr_injective (Sum.inr_injective h'')
      simp only [Prod.mk.injEq] at h1
      exact h1
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  have hjob_osl : ∀ e v c i, job e ≠ osl v c i := fun e v c i h => Sum.inl_ne_inr h
  have hjob_xsl : ∀ e v h k, job e ≠ xsl v h k := fun e v h k h' => Sum.inl_ne_inr h'
  have hosl_xsl : ∀ v c i v' h k, osl v c i ≠ xsl v' h k := fun v c i v' h k h' =>
    Sum.inl_ne_inr (Sum.inr_injective h')
  -- membership in the listed sets
  have m1job : ∀ e t, job e ∈ S₁ t ↔ t.1 = e := by
    intro e t
    simp only [S₁, Finset.mem_insert, Finset.mem_singleton, hjob_inj]
    constructor
    · rintro (h | h | h)
      · exact h.symm
      · exact absurd h (hjob_osl _ _ _ _)
      · exact absurd h (hjob_osl _ _ _ _)
    · intro h; exact Or.inl h.symm
  have m2job : ∀ e t, job e ∈ S₂ t ↔ t.1 = e := by
    intro e t
    simp only [S₂, Finset.mem_insert, Finset.mem_singleton, hjob_inj]
    constructor
    · rintro (h | h | h)
      · exact h.symm
      · exact absurd h (hjob_xsl _ _ _ _)
      · exact absurd h (hjob_xsl _ _ _ _)
    · intro h; exact Or.inl h.symm
  have m1osl : ∀ v c i t, osl v c i ∈ S₁ t ↔
      (v = src t.1 ∧ c = t.2.1 ∧ i = t.2.2.1) ∨ (v = tgt t.1 ∧ c = t.2.1 ∧ i = t.2.2.2) := by
    intro v c i t
    simp only [S₁, Finset.mem_insert, Finset.mem_singleton, hosl_inj]
    constructor
    · rintro (h | h | h)
      · exact absurd h.symm (hjob_osl _ _ _ _)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have m2osl : ∀ v c i t, osl v c i ∉ S₂ t := by
    intro v c i t h
    simp only [S₂, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact hjob_osl _ _ _ _ h.symm
    · exact hosl_xsl _ _ _ _ _ _ h
    · exact hosl_xsl _ _ _ _ _ _ h
  have m1xsl : ∀ v h k t, xsl v h k ∉ S₁ t := by
    intro v h k t h'
    simp only [S₁, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with h' | h' | h'
    · exact hjob_xsl _ _ _ _ h'.symm
    · exact hosl_xsl _ _ _ _ _ _ h'.symm
    · exact hosl_xsl _ _ _ _ _ _ h'.symm
  have m2xsl : ∀ v h k t, xsl v h k ∈ S₂ t ↔
      (v = src t.1 ∧ h = hF t.1 ∧ k = t.2.1) ∨ (v = tgt t.1 ∧ h = hF t.1 ∧ k = t.2.2) := by
    intro v h k t
    simp only [S₂, Finset.mem_insert, Finset.mem_singleton, hxsl_inj]
    constructor
    · rintro (h' | h' | h')
      · exact absurd h'.symm (hjob_xsl _ _ _ _)
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h' | h')
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  -- counting formulas
  have hdeg : ∀ (P : ι → Prop) [DecidablePred P] (P₁ : E × 𝒞 × Fin Ks × Fin Ks → Prop)
      (P₂ : E × Fin Bmax × Fin Bmax → Prop) [DecidablePred P₁] [DecidablePred P₂],
      (∀ t m, P (Sum.inl ⟨t, m⟩) ↔ P₁ t) → (∀ t m, P (Sum.inr ⟨t, m⟩) ↔ P₂ t) →
      (((Finset.univ : Finset ι).filter P).card : ℝ)
        = ∑ t, (if P₁ t then (M₁ t : ℝ) else 0) + ∑ t, (if P₂ t then (M₂ t : ℝ) else 0) := by
    intro P _ P₁ P₂ _ _ h₁ h₂
    rw [card_filter_sigma_sum M₁ M₂ P P₁ P₂ h₁ h₂]
    push_cast
    rfl
  -- size bounds for the multiplicities
  have hM₁le : ∀ t, (M₁ t : ℝ) ≤ N * XL t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    intro t
    rw [hM₁ t]
    split_ifs
    · exact Nat.floor_le (by have := hXL0 t.1 t.2.1 t.2.2.1 t.2.2.2; positivity)
    · simp only [Nat.cast_zero]; have := hXL0 t.1 t.2.1 t.2.2.1 t.2.2.2; positivity
  have hM₁ge : ∀ t, lg t.1 → (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 - 1 ≤ M₁ t := by
    intro t ht
    rw [hM₁ t, if_pos ht]
    have := Nat.lt_floor_add_one ((N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2)
    linarith
  have hcntB : ∀ B : ℕ, B ≤ Bmax → ∑ k : Fin Bmax, (if (k : ℕ) < B then (1 : ℝ) else 0) = B := by
    intro B hB
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    norm_cast
    rw [Fin.card_filter_val_lt]
    omega
  have hBvh_real : ∀ v h, (0 : ℝ) < Bvh v h := fun v h => by exact_mod_cast hBpos v h
  have hM₂row1 : ∀ e (k : Fin Bmax), ∑ k₂, (M₂ (e, k, k₂) : ℝ) ≤ N * rE e / Bvh (src e) (hF e) := by
    intro e k
    have hBs := hBvh_real (src e) (hF e)
    have hBt := hBvh_real (tgt e) (hF e)
    obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = (N : ℝ) * rE e / ((Bvh (src e) (hF e) : ℝ) * Bvh (tgt e) (hF e)) :=
      ⟨_, rfl⟩
    have hF0 : 0 ≤ F := by rw [hFdef]; have := hrE0 e; positivity
    have h1 : ∀ k₂ : Fin Bmax, (M₂ (e, k, k₂) : ℝ)
        ≤ if (k₂ : ℕ) < Bvh (tgt e) (hF e) then F else 0 := by
      intro k₂
      rw [hM₂ (e, k, k₂)]
      split_ifs with hv hk
      · rw [hFdef]; exact Nat.floor_le (hFdef ▸ hF0)
      · exact absurd hv.2.2 hk
      · simp [hF0]
      · simp
    calc ∑ k₂, (M₂ (e, k, k₂) : ℝ)
        ≤ ∑ k₂ : Fin Bmax, (if (k₂ : ℕ) < Bvh (tgt e) (hF e) then F else 0) :=
          Finset.sum_le_sum (fun k₂ _ => h1 k₂)
      _ = Bvh (tgt e) (hF e) * F := by
          rw [show (fun k₂ : Fin Bmax => if (k₂ : ℕ) < Bvh (tgt e) (hF e) then F else 0)
            = (fun k₂ : Fin Bmax => (if (k₂ : ℕ) < Bvh (tgt e) (hF e) then (1 : ℝ) else 0) * F) by
              funext k₂; split_ifs <;> simp]
          rw [← Finset.sum_mul, hcntB _ (hBlt _ _).le]
      _ = N * rE e / Bvh (src e) (hF e) := by
          rw [hFdef]; field_simp
  have hM₂row2 : ∀ e (k : Fin Bmax), ∑ k₁, (M₂ (e, k₁, k) : ℝ) ≤ N * rE e / Bvh (tgt e) (hF e) := by
    intro e k
    have hBs := hBvh_real (src e) (hF e)
    have hBt := hBvh_real (tgt e) (hF e)
    obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = (N : ℝ) * rE e / ((Bvh (src e) (hF e) : ℝ) * Bvh (tgt e) (hF e)) :=
      ⟨_, rfl⟩
    have hF0 : 0 ≤ F := by rw [hFdef]; have := hrE0 e; positivity
    have h1 : ∀ k₁ : Fin Bmax, (M₂ (e, k₁, k) : ℝ)
        ≤ if (k₁ : ℕ) < Bvh (src e) (hF e) then F else 0 := by
      intro k₁
      rw [hM₂ (e, k₁, k)]
      split_ifs with hv hk
      · rw [hFdef]; exact Nat.floor_le (hFdef ▸ hF0)
      · exact absurd hv.2.1 hk
      · simp [hF0]
      · simp
    calc ∑ k₁, (M₂ (e, k₁, k) : ℝ)
        ≤ ∑ k₁ : Fin Bmax, (if (k₁ : ℕ) < Bvh (src e) (hF e) then F else 0) :=
          Finset.sum_le_sum (fun k₁ _ => h1 k₁)
      _ = Bvh (src e) (hF e) * F := by
          rw [show (fun k₁ : Fin Bmax => if (k₁ : ℕ) < Bvh (src e) (hF e) then F else 0)
            = (fun k₁ : Fin Bmax => (if (k₁ : ℕ) < Bvh (src e) (hF e) then (1 : ℝ) else 0) * F) by
              funext k₁; split_ifs <;> simp]
          rw [← Finset.sum_mul, hcntB _ (hBlt _ _).le]
      _ = N * rE e / Bvh (tgt e) (hF e) := by
          rw [hFdef]; field_simp
  have hM₂full : ∀ e, lg e → (N : ℝ) * rE e - Bvh (src e) (hF e) * Bvh (tgt e) (hF e)
      ≤ ∑ k₁, ∑ k₂, (M₂ (e, k₁, k₂) : ℝ) := by
    intro e he
    have hBs := hBvh_real (src e) (hF e)
    have hBt := hBvh_real (tgt e) (hF e)
    obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = (N : ℝ) * rE e / ((Bvh (src e) (hF e) : ℝ) * Bvh (tgt e) (hF e)) :=
      ⟨_, rfl⟩
    have h1 : ∀ k₁ k₂ : Fin Bmax, (M₂ (e, k₁, k₂) : ℝ)
        = (if (k₁ : ℕ) < Bvh (src e) (hF e) then (1 : ℝ) else 0) *
          ((if (k₂ : ℕ) < Bvh (tgt e) (hF e) then (1 : ℝ) else 0) * (⌊F⌋₊ : ℝ)) := by
      intro k₁ k₂
      rw [hM₂ (e, k₁, k₂), hFdef]
      by_cases h₁ : (k₁ : ℕ) < Bvh (src e) (hF e) <;> by_cases h₂ : (k₂ : ℕ) < Bvh (tgt e) (hF e)
      · rw [if_pos ⟨he, h₁, h₂⟩]; simp [h₁, h₂]
      · rw [if_neg (fun h => h₂ h.2.2)]; simp [h₂]
      · rw [if_neg (fun h => h₁ h.2.1)]; simp [h₁]
      · rw [if_neg (fun h => h₁ h.2.1)]; simp [h₁]
    simp_rw [h1, ← Finset.mul_sum, ← Finset.sum_mul, hcntB _ (hBlt _ _).le]
    have := Nat.lt_floor_add_one F
    have hFe : (Bvh (src e) (hF e) : ℝ) * Bvh (tgt e) (hF e) * F = N * rE e := by
      rw [hFdef]; field_simp
    have h4 : (Bvh (src e) (hF e) : ℝ) * Bvh (tgt e) (hF e) * F
        ≤ Bvh (src e) (hF e) * Bvh (tgt e) (hF e) * (⌊F⌋₊ + 1) :=
      mul_le_mul_of_nonneg_left this.le (mul_pos hBs hBt).le
    linarith
  -- splitting sums over tuples
  have hsplitE : ∀ {R : Type} [Fintype R] (e : E) (g : E × R → ℝ),
      ∑ t : E × R, (if t.1 = e then g t else 0) = ∑ r, g (e, r) := by
    intro R _ e g
    rw [Fintype.sum_prod_type, Finset.sum_eq_single e]
    · simp
    · intro e' _ he'; simp [he']
    · simp
  have hsum3 : ∀ (e : E) (g : 𝒞 → Fin Ks → Fin Ks → ℝ),
      ∑ r : 𝒞 × Fin Ks × Fin Ks, g r.1 r.2.1 r.2.2 = ∑ c, ∑ i, ∑ j, g c i j := by
    intro e g; simp only [Fintype.sum_prod_type]
  -- the scale
  have hmn : n ≤ m := by rw [hm]; exact Nat.le_ceil n
  have hm2n : (m : ℝ) ≤ 2 * n := by
    rw [hm]; have := Nat.ceil_lt_add_one hn0.le; linarith
  have hN6 : n ^ 6 ≤ (N : ℝ) := by
    rw [hN]; push_cast; exact pow_le_pow_left₀ hn0.le hmn 6
  have hn6 : n ≤ n ^ 6 := by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ 6 := pow_le_pow_right₀ hn1 (by norm_num)
  have hn4 : n ≤ n ^ 4 := by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN6
  have hDN : D ≥ N / 2 := by
    rw [hD]
    have : 0 ≤ (1 / 2 - η / 2) * (N : ℝ) :=
      mul_nonneg (by linarith [le_trans hηlam hlam8]) hNpos.le
    linarith
  have hDn : n / 2 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  have hn23 : n ^ (2 / 3 : ℝ) ≤ n := by
    calc n ^ (2 / 3 : ℝ) ≤ n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = n := Real.rpow_one n
  have hn23pos : 0 < n ^ (2 / 3 : ℝ) := by positivity
  -- bounds on the numbers of extra slots
  have hRvh_le : ∀ v h, Rvh v h ≤ n / β := by
    intro v h
    rw [hRvh]
    calc ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e
        ≤ ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), G.w e / β := by
          apply Finset.sum_le_sum
          intro e he
          have hlg : β ≤ G.w e := (Finset.mem_filter.mp he).2.1
          rw [le_div_iff₀ hβ0]
          have := mul_le_of_le_one_left hβ0.le (hrE1 e)
          linarith
      _ ≤ ∑ e ∈ G.inc v, G.w e / β := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro e _ _; exact div_nonneg (G.w_pos e).le hβ0.le
      _ = G.W v / β := by unfold WGraph.W; rw [Finset.sum_div]
      _ ≤ n / β := div_le_div_of_nonneg_right (hW v) hβ0.le
  have hBvh_le : ∀ v h, (Bvh v h : ℝ) ≤ cB * n := by
    intro v h
    rw [hBvh]
    push_cast
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ Rvh v h / (1 - lam) by
      apply div_nonneg _ (by linarith)
      rw [hRvh]; exact Finset.sum_nonneg (fun e _ => hrE0 e))
    have h2 : (T : ℝ) ≤ n ^ (2 / 3 : ℝ) + 1 := by
      rw [hT]; exact (Nat.ceil_lt_add_one (by positivity)).le
    have h3 : Rvh v h / (1 - lam) ≤ 2 * n / β := by
      have hnb : 0 ≤ n / β := by positivity
      calc Rvh v h / (1 - lam) ≤ (n / β) / (1 - lam) :=
            div_le_div_of_nonneg_right (hRvh_le v h) (by linarith)
        _ ≤ 2 * n / β := by
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - lam),
              show 2 * n / β * (1 - lam) = n / β * (2 * (1 - lam)) by ring]
            exact le_mul_of_one_le_right hnb (by linarith)
    have : (2 / β + 4) * n = 2 * n / β + 4 * n := by ring
    rw [hcB, this]
    linarith
  have hcB0 : 0 < cB := by rw [hcB]; positivity
  -- job degrees
  have hDa : D ^ (-a) ≤ η / 4 := by
    have h1 : (4 / η) ^ (1 / a) ≤ D := by linarith
    have h2 : 4 / η ≤ D ^ a := by
      have := Real.rpow_le_rpow (by positivity) h1 ha0.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel ha0.ne', Real.rpow_one] at this
    rw [Real.rpow_neg hD0.le]
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
    exact h2
  have hcLN : cL * n ^ 2 ≤ η / 4 * N := by
    have h1 : cL ≤ η / 4 * n ^ 4 := by
      have := hnL
      rw [div_le_iff₀ hη0] at this
      have := mul_le_mul_of_nonneg_left hn4 hη0.le
      linarith
    have h2 : n ^ 6 = n ^ 4 * n ^ 2 := by ring
    have h3 := mul_le_mul_of_nonneg_right h1 (sq_nonneg n)
    have h4 : η / 4 * n ^ 6 ≤ η / 4 * N := mul_le_mul_of_nonneg_left hN6 (by positivity)
    have h5 : η / 4 * n ^ 4 * n ^ 2 = η / 4 * n ^ 6 := by ring
    linarith
  have hdegA : ∀ x ∈ A, (1 + D ^ (-a)) * D ≤ ((Finset.univ.filter (fun i => x ∈ S i)).card : ℝ) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hAjob x hx
    rw [hdeg (fun i => job e ∈ S i) (fun t => t.1 = e) (fun t => t.1 = e) (fun t _ => m1job e t)
      (fun t _ => m2job e t)]
    rw [hsplitE e (fun t => (M₁ t : ℝ)), hsplitE e (fun t => (M₂ t : ℝ))]
    have hp1 : (N : ℝ) * sE e - (Fintype.card 𝒞 * (Ks * Ks) : ℕ) ≤ ∑ r : 𝒞 × Fin Ks × Fin Ks, (M₁ (e, r) : ℝ) := by
      calc (N : ℝ) * sE e - (Fintype.card 𝒞 * (Ks * Ks) : ℕ)
          = ∑ r : 𝒞 × Fin Ks × Fin Ks, ((N : ℝ) * XL e r.1 r.2.1 r.2.2 - 1) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum3 e (fun c i j => XL e c i j), hsEdef]
            simp
        _ ≤ ∑ r : 𝒞 × Fin Ks × Fin Ks, (M₁ (e, r) : ℝ) :=
            Finset.sum_le_sum (fun r _ => hM₁ge (e, r) he)
    have hp2 := hM₂full e he
    rw [show ∑ r : Fin Bmax × Fin Bmax, (M₂ (e, r) : ℝ) = ∑ k₁, ∑ k₂, (M₂ (e, k₁, k₂) : ℝ) by
      rw [Fintype.sum_prod_type]]
    have hsr : sE e + rE e = 1 := by rw [hrEdef]; ring
    have hc : ((Fintype.card 𝒞 * (Ks * Ks) : ℕ) : ℝ) ≤ C₁ * (Ks : ℝ) ^ 2 * n ^ 2 := by
      push_cast
      have : (Fintype.card 𝒞 : ℝ) ≤ C₁ * n ^ 2 := by
        have := mul_le_mul_of_nonneg_left (le_self_pow₀ hn1 (by norm_num : (2 : ℕ) ≠ 0)) hC₁.le
        linarith
      have h' := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ (Ks : ℝ) * Ks)
      have : C₁ * n ^ 2 * ((Ks : ℝ) * Ks) = C₁ * (Ks : ℝ) ^ 2 * n ^ 2 := by ring
      linarith
    have hBB : (Bvh (src e) (hF e) : ℝ) * Bvh (tgt e) (hF e) ≤ cB ^ 2 * n ^ 2 := by
      have h1 := hBvh_le (src e) (hF e)
      have h2 := hBvh_le (tgt e) (hF e)
      have h3 : (0 : ℝ) ≤ Bvh (src e) (hF e) := (hBvh_real _ _).le
      calc (Bvh (src e) (hF e) : ℝ) * Bvh (tgt e) (hF e) ≤ (cB * n) * (cB * n) :=
            mul_le_mul h1 h2 (hBvh_real _ _).le (by positivity)
        _ = cB ^ 2 * n ^ 2 := by ring
    have hlow : (N : ℝ) - cL * n ^ 2 ≤ ∑ r : 𝒞 × Fin Ks × Fin Ks, (M₁ (e, r) : ℝ)
        + ∑ k₁, ∑ k₂, (M₂ (e, k₁, k₂) : ℝ) := by
      have e1 : (N : ℝ) * sE e + N * rE e = N := by rw [← mul_add, hsr, mul_one]
      have e2 : cL * n ^ 2 = C₁ * (Ks : ℝ) ^ 2 * n ^ 2 + cB ^ 2 * n ^ 2 := by rw [hcL]; ring
      linarith
    have hup : (1 + D ^ (-a)) * D ≤ (1 - η / 4) * N := by
      have h1 : (1 + D ^ (-a)) * D ≤ (1 + η / 4) * D :=
        mul_le_mul_of_nonneg_right (by linarith) hD0.le
      have h2 : (1 + η / 4) * D = (1 - η / 4) * N - η ^ 2 / 8 * N := by rw [hD]; ring
      have h3 : 0 ≤ η ^ 2 / 8 * N := by positivity
      linarith
    linarith
  -- slot degrees
  have hite_or : ∀ (P Q : Prop) [Decidable P] [Decidable Q] (x : ℝ), 0 ≤ x →
      (if P ∨ Q then x else 0) ≤ (if P then x else 0) + (if Q then x else 0) := by
    intro P Q _ _ x hx
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, hx]
  have hM₁0 : ∀ t, (0 : ℝ) ≤ M₁ t := fun t => Nat.cast_nonneg _
  have hM₂0 : ∀ t, (0 : ℝ) ≤ M₂ t := fun t => Nat.cast_nonneg _
  have hosl_deg : ∀ v c i, ((Finset.univ.filter (fun ι' => osl v c i ∈ S ι')).card : ℝ) ≤ D := by
    intro v c i
    rw [hdeg (fun ι' => osl v c i ∈ S ι') (fun t => osl v c i ∈ S₁ t) (fun t => osl v c i ∈ S₂ t)
      (fun t _ => Iff.rfl) (fun t _ => Iff.rfl)]
    simp only [m2osl, if_false, Finset.sum_const_zero, add_zero]
    refine le_trans (Finset.sum_le_sum (fun t _ => ?_)) (b := ∑ t : E × 𝒞 × Fin Ks × Fin Ks,
      ((if v = src t.1 ∧ c = t.2.1 ∧ i = t.2.2.1 then (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0)
        + (if v = tgt t.1 ∧ c = t.2.1 ∧ i = t.2.2.2 then (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0))) ?_
    · have hX : (0 : ℝ) ≤ N * XL t.1 t.2.1 t.2.2.1 t.2.2.2 :=
        mul_nonneg (Nat.cast_nonneg _) (hXL0 _ _ _ _)
      have hi1 : (0 : ℝ) ≤ (if v = src t.1 ∧ c = t.2.1 ∧ i = t.2.2.1 then
          (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0) := by split_ifs <;> simp [hX]
      have hi2 : (0 : ℝ) ≤ (if v = tgt t.1 ∧ c = t.2.1 ∧ i = t.2.2.2 then
          (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0) := by split_ifs <;> simp [hX]
      by_cases hm : osl v c i ∈ S₁ t
      · rw [if_pos hm]
        rcases (m1osl v c i t).mp hm with h | h
        · rw [if_pos h]; linarith [hM₁le t]
        · rw [if_pos h]; linarith [hM₁le t]
      · rw [if_neg hm]; linarith
    rw [Finset.sum_add_distrib]
    have e1 : ∑ t : E × 𝒞 × Fin Ks × Fin Ks,
        (if v = src t.1 ∧ c = t.2.1 ∧ i = t.2.2.1 then (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0)
        = N * ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j := by
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _
      by_cases he : src e = v
      · simp [he, ite_and, Finset.mul_sum]
      · simp [he, Ne.symm he]
    have e2 : ∑ t : E × 𝒞 × Fin Ks × Fin Ks,
        (if v = tgt t.1 ∧ c = t.2.1 ∧ i = t.2.2.2 then (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0)
        = N * ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i := by
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _
      by_cases he : tgt e = v
      · simp [he, ite_and, Finset.mul_sum]
      · simp [he, Ne.symm he]
    rw [e1, e2, ← mul_add]
    have hl := hslot v c i
    calc (N : ℝ) * (∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
          + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i)
        ≤ N * (1 - σ) := mul_le_mul_of_nonneg_left hl hNpos.le
      _ ≤ D := by
          rw [hD, mul_comm]
          exact mul_le_mul_of_nonneg_right (by linarith) hNpos.le
  have hM₂lg : ∀ t, ¬ lg t.1 → M₂ t = 0 := by
    intro t ht; rw [hM₂ t, if_neg (fun h => ht h.1)]
  have hxsl_deg : ∀ v h k, ((Finset.univ.filter (fun ι' => xsl v h k ∈ S ι')).card : ℝ) ≤ D := by
    intro v h k
    rw [hdeg (fun ι' => xsl v h k ∈ S ι') (fun t => xsl v h k ∈ S₁ t) (fun t => xsl v h k ∈ S₂ t)
      (fun t _ => Iff.rfl) (fun t _ => Iff.rfl)]
    simp only [m1xsl, if_false, Finset.sum_const_zero, zero_add]
    -- the two halves
    refine le_trans (Finset.sum_le_sum (fun t _ => ?_)) (b := ∑ t : E × Fin Bmax × Fin Bmax,
      ((if v = src t.1 ∧ h = hF t.1 ∧ k = t.2.1 then (M₂ t : ℝ) else 0)
        + (if v = tgt t.1 ∧ h = hF t.1 ∧ k = t.2.2 then (M₂ t : ℝ) else 0))) ?_
    · have hi1 : (0 : ℝ) ≤ (if v = src t.1 ∧ h = hF t.1 ∧ k = t.2.1 then (M₂ t : ℝ) else 0) := by
        split_ifs <;> simp
      have hi2 : (0 : ℝ) ≤ (if v = tgt t.1 ∧ h = hF t.1 ∧ k = t.2.2 then (M₂ t : ℝ) else 0) := by
        split_ifs <;> simp
      by_cases hm : xsl v h k ∈ S₂ t
      · rw [if_pos hm]
        rcases (m2xsl v h k t).mp hm with h' | h'
        · rw [if_pos h']; linarith
        · rw [if_pos h']; linarith
      · rw [if_neg hm]; linarith
    rw [Finset.sum_add_distrib]
    have e1 : ∑ t : E × Fin Bmax × Fin Bmax, (if v = src t.1 ∧ h = hF t.1 ∧ k = t.2.1 then (M₂ t : ℝ) else 0)
        = ∑ e, if v = src e ∧ h = hF e then ∑ k₂, (M₂ (e, k, k₂) : ℝ) else 0 := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro e _
      by_cases he : v = src e ∧ h = hF e
      · simp [he, ite_and]
      · simp only [he, if_false]
        apply Finset.sum_eq_zero; intro k₁ _; apply Finset.sum_eq_zero; intro k₂ _
        rw [if_neg]; intro hc; exact he ⟨hc.1, hc.2.1⟩
    have e2 : ∑ t : E × Fin Bmax × Fin Bmax, (if v = tgt t.1 ∧ h = hF t.1 ∧ k = t.2.2 then (M₂ t : ℝ) else 0)
        = ∑ e, if v = tgt e ∧ h = hF e then ∑ k₁, (M₂ (e, k₁, k) : ℝ) else 0 := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro e _
      by_cases he : v = tgt e ∧ h = hF e
      · rw [if_pos he]
        apply Finset.sum_congr rfl; intro k₁ _
        rw [Finset.sum_eq_single k]
        · rw [if_pos ⟨he.1, he.2, rfl⟩]
        · intro k₂ _ hk₂; rw [if_neg]; intro hc; exact hk₂ hc.2.2.symm
        · simp
      · simp only [he, if_false]
        apply Finset.sum_eq_zero; intro k₁ _; apply Finset.sum_eq_zero; intro k₂ _
        rw [if_neg]; intro hc; exact he ⟨hc.1, hc.2.1⟩
    rw [e1, e2, ← Finset.sum_add_distrib]
    have hpt : ∀ e, ((if v = src e ∧ h = hF e then ∑ k₂, (M₂ (e, k, k₂) : ℝ) else 0)
        + (if v = tgt e ∧ h = hF e then ∑ k₁, (M₂ (e, k₁, k) : ℝ) else 0))
        ≤ if v ∈ G.ends e then (if lg e ∧ hF e = h then N * rE e / Bvh v h else 0) else 0 := by
      intro e
      by_cases hlg : lg e
      · by_cases h1 : v = src e ∧ h = hF e
        · have h2 : ¬ (v = tgt e ∧ h = hF e) := fun h2 => hst_ne e (h1.1.symm.trans h2.1)
          rw [if_pos h1, if_neg h2, add_zero, if_pos ((hmem e v).mpr (Or.inl h1.1)),
            if_pos ⟨hlg, h1.2.symm⟩]
          have := hM₂row1 e k
          rw [← h1.1, ← h1.2] at this
          exact this
        · by_cases h2 : v = tgt e ∧ h = hF e
          · rw [if_neg h1, if_pos h2, zero_add, if_pos ((hmem e v).mpr (Or.inr h2.1)),
              if_pos ⟨hlg, h2.2.symm⟩]
            have := hM₂row2 e k
            rw [← h2.1, ← h2.2] at this
            exact this
          · rw [if_neg h1, if_neg h2, add_zero]
            have : (0 : ℝ) ≤ N * rE e / Bvh v h :=
              div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hrE0 e)) (hBvh_real v h).le
            split_ifs <;> linarith
      · have z1 : ∑ k₂, (M₂ (e, k, k₂) : ℝ) = 0 :=
          Finset.sum_eq_zero (fun k₂ _ => by rw [hM₂lg (e, k, k₂) hlg]; simp)
        have z2 : ∑ k₁, (M₂ (e, k₁, k) : ℝ) = 0 :=
          Finset.sum_eq_zero (fun k₁ _ => by rw [hM₂lg (e, k₁, k) hlg]; simp)
        rw [z1, z2]
        simp only [ite_self, add_zero]
        by_cases hv : v ∈ G.ends e
        · rw [if_pos hv, if_neg (fun h' : lg e ∧ hF e = h => hlg h'.1)]
        · rw [if_neg hv]
    refine le_trans (Finset.sum_le_sum (fun e _ => hpt e)) ?_
    rw [← Finset.sum_filter]
    have hfilt : ∑ e ∈ Finset.univ.filter (fun e => v ∈ G.ends e),
        (if lg e ∧ hF e = h then (N : ℝ) * rE e / Bvh v h else 0) = N / Bvh v h * Rvh v h := by
      rw [hRvh, Finset.mul_sum, ← Finset.sum_filter]
      unfold WGraph.inc
      rw [Finset.filter_filter]
      apply Finset.sum_congr rfl; intro e _; ring
    rw [hfilt]
    have hB := hBvh_real v h
    have hR : Rvh v h ≤ (1 - lam) * Bvh v h := by
      have h1 : Rvh v h / (1 - lam) ≤ ⌈Rvh v h / (1 - lam)⌉₊ := Nat.le_ceil _
      have h2 : (⌈Rvh v h / (1 - lam)⌉₊ : ℝ) ≤ Bvh v h := by
        rw [hBvh]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) T]
      rw [div_le_iff₀ (by linarith)] at h1
      have := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ 1 - lam)
      linarith
    calc (N : ℝ) / Bvh v h * Rvh v h ≤ N / Bvh v h * ((1 - lam) * Bvh v h) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
      _ = (1 - lam) * N := by field_simp
      _ ≤ D := by
          rw [hD]
          exact mul_le_mul_of_nonneg_right (by linarith) hNpos.le
  have hdegB : ∀ y ∈ Bs, ((Finset.univ.filter (fun ι' => y ∈ S ι')).card : ℝ) ≤ D := by
    intro y hy
    rcases y with e | (p | p)
    · exact absurd hy (hjobB e)
    · exact hosl_deg p.1 p.2.1 p.2.2
    · exact hxsl_deg p.1 p.2.1 p.2.2
  -- codegrees
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = (Cm + 2) * N / n ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  have hcod_jo : ∀ e v c i,
      ((Finset.univ.filter (fun ι' => job e ∈ S ι' ∧ osl v c i ∈ S ι')).card : ℝ) ≤ N * Cm / n := by
    intro e v c i
    rw [hdeg (fun ι' => job e ∈ S ι' ∧ osl v c i ∈ S ι') (fun t => job e ∈ S₁ t ∧ osl v c i ∈ S₁ t)
      (fun t => job e ∈ S₂ t ∧ osl v c i ∈ S₂ t) (fun t _ => Iff.rfl) (fun t _ => Iff.rfl)]
    simp only [m2osl, and_false, if_false, Finset.sum_const_zero, add_zero]
    refine le_trans (Finset.sum_le_sum (fun t _ => ?_)) (b := ∑ t : E × 𝒞 × Fin Ks × Fin Ks,
      (if t.1 = e ∧ t.2.1 = c then (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0)) ?_
    · by_cases hm : job e ∈ S₁ t ∧ osl v c i ∈ S₁ t
      · rw [if_pos hm]
        have h1 := (m1job e t).mp hm.1
        have h2 : c = t.2.1 := by
          rcases (m1osl v c i t).mp hm.2 with h | h
          · exact h.2.1
          · exact h.2.1
        rw [if_pos ⟨h1, h2.symm⟩]
        exact hM₁le t
      · rw [if_neg hm]
        split_ifs
        · exact mul_nonneg (Nat.cast_nonneg _) (hXL0 _ _ _ _)
        · exact le_refl _
    have e1 : ∑ t : E × 𝒞 × Fin Ks × Fin Ks,
        (if t.1 = e ∧ t.2.1 = c then (N : ℝ) * XL t.1 t.2.1 t.2.2.1 t.2.2.2 else 0)
        = N * ∑ i', ∑ j', XL e c i' j' := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single e]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
        · simp only [and_self, if_true, Fintype.sum_prod_type, Finset.mul_sum]
        · intro c' _ hc'; simp [hc']
        · simp
      · intro e' _ he'; simp [he']
      · simp
    rw [e1]
    have := hmass e c
    calc (N : ℝ) * ∑ i', ∑ j', XL e c i' j' ≤ N * (Cm / n) :=
          mul_le_mul_of_nonneg_left this hNpos.le
      _ = N * Cm / n := by ring
  have hcod_jx : ∀ e v h k,
      ((Finset.univ.filter (fun ι' => job e ∈ S ι' ∧ xsl v h k ∈ S ι')).card : ℝ) ≤ 2 * N / T := by
    intro e v h k
    rw [hdeg (fun ι' => job e ∈ S ι' ∧ xsl v h k ∈ S ι') (fun t => job e ∈ S₁ t ∧ xsl v h k ∈ S₁ t)
      (fun t => job e ∈ S₂ t ∧ xsl v h k ∈ S₂ t) (fun t _ => Iff.rfl) (fun t _ => Iff.rfl)]
    simp only [m1xsl, and_false, if_false, Finset.sum_const_zero, zero_add]
    refine le_trans (Finset.sum_le_sum (fun t _ => ?_)) (b := ∑ t : E × Fin Bmax × Fin Bmax,
      ((if t.1 = e ∧ k = t.2.1 then (M₂ t : ℝ) else 0) + (if t.1 = e ∧ k = t.2.2 then (M₂ t : ℝ) else 0))) ?_
    · have hi1 : (0 : ℝ) ≤ (if t.1 = e ∧ k = t.2.1 then (M₂ t : ℝ) else 0) := by split_ifs <;> simp
      have hi2 : (0 : ℝ) ≤ (if t.1 = e ∧ k = t.2.2 then (M₂ t : ℝ) else 0) := by split_ifs <;> simp
      by_cases hm : job e ∈ S₂ t ∧ xsl v h k ∈ S₂ t
      · rw [if_pos hm]
        have h1 := (m2job e t).mp hm.1
        rcases (m2xsl v h k t).mp hm.2 with h' | h'
        · rw [if_pos (show t.1 = e ∧ k = t.2.1 from ⟨h1, h'.2.2⟩)]; linarith
        · rw [if_pos (show t.1 = e ∧ k = t.2.2 from ⟨h1, h'.2.2⟩)]; linarith
      · rw [if_neg hm]; linarith
    rw [Finset.sum_add_distrib]
    have e1 : ∑ t : E × Fin Bmax × Fin Bmax, (if t.1 = e ∧ k = t.2.1 then (M₂ t : ℝ) else 0)
        = ∑ k₂, (M₂ (e, k, k₂) : ℝ) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single e]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
        · simp
        · intro k' _ hk'; apply Finset.sum_eq_zero; intro k₂ _; rw [if_neg]; intro hc; exact hk' hc.2.symm
        · simp
      · intro e' _ he'; apply Finset.sum_eq_zero; intro r _; rw [if_neg]; intro hc; exact he' hc.1
      · simp
    have e2 : ∑ t : E × Fin Bmax × Fin Bmax, (if t.1 = e ∧ k = t.2.2 then (M₂ t : ℝ) else 0)
        = ∑ k₁, (M₂ (e, k₁, k) : ℝ) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single e]
      · rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro k₁ _
        rw [Finset.sum_eq_single k]
        · simp
        · intro k' _ hk'; rw [if_neg]; intro hc; exact hk' hc.2.symm
        · simp
      · intro e' _ he'; apply Finset.sum_eq_zero; intro r _; rw [if_neg]; intro hc; exact he' hc.1
      · simp
    rw [e1, e2]
    have h1 := hM₂row1 e k
    have h2 := hM₂row2 e k
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
    have hb1 : (N : ℝ) * rE e / Bvh (src e) (hF e) ≤ N / T := by
      have hTB : (T : ℝ) ≤ Bvh (src e) (hF e) := by rw [hBvh]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈Rvh (src e) (hF e) / (1 - lam)⌉₊]
      calc (N : ℝ) * rE e / Bvh (src e) (hF e) ≤ N * 1 / Bvh (src e) (hF e) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hrE1 e) hNpos.le) (hBvh_real _ _).le
        _ ≤ N / T := by rw [mul_one]; exact div_le_div_of_nonneg_left hNpos.le hT0 hTB
    have hb2 : (N : ℝ) * rE e / Bvh (tgt e) (hF e) ≤ N / T := by
      have hTB : (T : ℝ) ≤ Bvh (tgt e) (hF e) := by rw [hBvh]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈Rvh (tgt e) (hF e) / (1 - lam)⌉₊]
      calc (N : ℝ) * rE e / Bvh (tgt e) (hF e) ≤ N * 1 / Bvh (tgt e) (hF e) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hrE1 e) hNpos.le) (hBvh_real _ _).le
        _ ≤ N / T := by rw [mul_one]; exact div_le_div_of_nonneg_left hNpos.le hT0 hTB
    have : 2 * (N : ℝ) / T = N / T + N / T := by ring
    linarith
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; positivity
  have hΔ1 : (N : ℝ) * Cm / n ≤ Δ := by
    rw [hΔ]
    calc (N : ℝ) * Cm / n ≤ N * Cm / n ^ (2 / 3 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hn23pos hn23
      _ ≤ (Cm + 2) * N / n ^ (2 / 3 : ℝ) := by
          apply div_le_div_of_nonneg_right _ hn23pos.le
          nlinarith only [hNpos]
  have hΔ2 : 2 * (N : ℝ) / T ≤ Δ := by
    rw [hΔ]
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
    calc 2 * (N : ℝ) / T ≤ 2 * N / n ^ (2 / 3 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hn23pos hTn
      _ ≤ (Cm + 2) * N / n ^ (2 / 3 : ℝ) := by
          apply div_le_div_of_nonneg_right _ hn23pos.le
          nlinarith only [hNpos, hCm]
  have hjs : ∀ e (y : α), (∀ e', y ≠ job e') →
      ((Finset.univ.filter (fun ι' => job e ∈ S ι' ∧ y ∈ S ι')).card : ℝ) ≤ Δ := by
    intro e y hy
    rcases y with e' | (p | p)
    · exact absurd rfl (hy e')
    · exact le_trans (hcod_jo e p.1 p.2.1 p.2.2) hΔ1
    · exact le_trans (hcod_jx e p.1 p.2.1 p.2.2) hΔ2
  let jb : ι → E := fun i => Sum.elim (fun i : (Σ t, Fin (M₁ t)) => i.1.1)
    (fun i : (Σ t, Fin (M₂ t)) => i.1.1) i
  have hjb : ∀ i e, job e ∈ S i ↔ jb i = e := by
    intro i e
    rcases i with ⟨t, m⟩ | ⟨t, m⟩
    · exact m1job e t
    · exact m2job e t
  let vert : α → V := fun x => Sum.elim src (Sum.elim (fun p : V × 𝒞 × Fin Ks => p.1)
    (fun p : V × Fin (Hm + 1) × Fin Bmax => p.1)) x
  have hpair : ∀ i x y, x ∈ S i → y ∈ S i → x ≠ y → (∀ e, x ≠ job e) → (∀ e, y ≠ job e) →
      G.ends (jb i) = s(vert x, vert y) := by
    intro i x y hx hy hxy hxj hyj
    rcases i with ⟨t, m⟩ | ⟨t, m⟩
    · change x ∈ S₁ t at hx
      change y ∈ S₁ t at hy
      change G.ends t.1 = _
      simp only [S₁, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl
      · exact absurd rfl (hxj _)
      · rcases hy with rfl | rfl | rfl
        · exact absurd rfl (hyj _)
        · exact absurd rfl hxy
        · exact hst t.1
      · rcases hy with rfl | rfl | rfl
        · exact absurd rfl (hyj _)
        · rw [Sym2.eq_swap]; exact hst t.1
        · exact absurd rfl hxy
    · change x ∈ S₂ t at hx
      change y ∈ S₂ t at hy
      change G.ends t.1 = _
      simp only [S₂, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl
      · exact absurd rfl (hxj _)
      · rcases hy with rfl | rfl | rfl
        · exact absurd rfl (hyj _)
        · exact absurd rfl hxy
        · exact hst t.1
      · rcases hy with rfl | rfl | rfl
        · exact absurd rfl (hyj _)
        · rw [Sym2.eq_swap]; exact hst t.1
        · exact absurd rfl hxy
  have hnotjob : ∀ p : (V × 𝒞 × Fin Ks) ⊕ (V × Fin (Hm + 1) × Fin Bmax), ∀ e,
      (Sum.inr p : α) ≠ job e := fun p e h => Sum.inr_ne_inl h
  have hcodΔ : ∀ x y : α, x ≠ y →
      ((Finset.univ.filter (fun ι' => x ∈ S ι' ∧ y ∈ S ι')).card : ℝ) ≤ Δ := by
    intro x y hxy
    rcases x with e | px <;> rcases y with e' | py
    · have : (Finset.univ.filter (fun ι' => job e ∈ S ι' ∧ job e' ∈ S ι')) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _ hi
        have h1 := (hjb i e).mp hi.1
        have h2 := (hjb i e').mp hi.2
        exact hxy (by rw [← h1, ← h2])
      change ((Finset.univ.filter (fun ι' => job e ∈ S ι' ∧ job e' ∈ S ι')).card : ℝ) ≤ Δ
      rw [this]; simpa using hΔ0
    · exact hjs e (Sum.inr py) (hnotjob py)
    · have := hjs e' (Sum.inr px) (hnotjob px)
      rw [Finset.filter_congr (fun i _ => and_comm)]
      exact this
    · set F := Finset.univ.filter (fun ι' => (Sum.inr px : α) ∈ S ι' ∧ (Sum.inr py : α) ∈ S ι')
      rcases F.eq_empty_or_nonempty with hF0 | ⟨i₀, hi₀⟩
      · rw [hF0]; simpa using hΔ0
      · have hi₀' := (Finset.mem_filter.mp hi₀).2
        have hsub : F ⊆ Finset.univ.filter (fun ι' => job (jb i₀) ∈ S ι' ∧ (Sum.inr px : α) ∈ S ι') := by
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, hi'.1⟩
          rw [hjb]
          apply hG
          rw [hpair i _ _ hi'.1 hi'.2 hxy (hnotjob px) (hnotjob py),
            hpair i₀ _ _ hi₀'.1 hi₀'.2 hxy (hnotjob px) (hnotjob py)]
        calc (F.card : ℝ) ≤ (Finset.univ.filter
              (fun ι' => job (jb i₀) ∈ S ι' ∧ (Sum.inr px : α) ∈ S ι')).card := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ Δ := hjs (jb i₀) (Sum.inr px) (hnotjob px)
  -- the asymptotic codegree bound
  have hΔ3 : Δ ≤ D ^ (1 - 1 / 10 : ℝ) := by
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hn0 hmn
    have hN10 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * n ^ (3 / 5 : ℝ) := by
      have h1 : (N : ℝ) ^ (1 / 10 : ℝ) = (m : ℝ) ^ (3 / 5 : ℝ) := by
        rw [hN, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
      rw [h1]
      calc (m : ℝ) ^ (3 / 5 : ℝ) ≤ (2 * n) ^ (3 / 5 : ℝ) :=
            Real.rpow_le_rpow hm0.le hm2n (by norm_num)
        _ = 2 ^ (3 / 5 : ℝ) * n ^ (3 / 5 : ℝ) := Real.mul_rpow (by norm_num) hn0.le
        _ ≤ 2 * n ^ (3 / 5 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc (2 : ℝ) ^ (3 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    have hsplitN : (N : ℝ) = N ^ (9 / 10 : ℝ) * N ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_add hNpos]; norm_num
    have hdom : 4 * (Cm + 2) * n ^ (3 / 5 : ℝ) ≤ n ^ (2 / 3 : ℝ) :=
      rpow_dominate (4 * (Cm + 2)) (3 / 5) (2 / 3) (by positivity) (by norm_num) n hn1 hnC
    have hN9 : (0 : ℝ) ≤ N ^ (9 / 10 : ℝ) := by positivity
    have hstep1 : Δ ≤ N ^ (9 / 10 : ℝ) / 2 := by
      rw [hΔ, div_le_div_iff₀ hn23pos (by norm_num)]
      have h0 : (Cm + 2) * (N : ℝ) * 2 = (Cm + 2) * (N ^ (9 / 10 : ℝ) * N ^ (1 / 10 : ℝ)) * 2 := by
        rw [← hsplitN]
      have : (Cm + 2) * (N ^ (9 / 10 : ℝ) * N ^ (1 / 10 : ℝ)) * 2
          ≤ (Cm + 2) * (N ^ (9 / 10 : ℝ) * (2 * n ^ (3 / 5 : ℝ))) * 2 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hN10 hN9
      have h2 : (Cm + 2) * (N ^ (9 / 10 : ℝ) * (2 * n ^ (3 / 5 : ℝ))) * 2
          = N ^ (9 / 10 : ℝ) * (4 * (Cm + 2) * n ^ (3 / 5 : ℝ)) := by ring
      have h3 := mul_le_mul_of_nonneg_left hdom hN9
      linarith
    have hstep2 : (N : ℝ) ^ (9 / 10 : ℝ) / 2 ≤ D ^ (1 - 1 / 10 : ℝ) := by
      have h1 : ((N : ℝ) / 2) ^ (9 / 10 : ℝ) ≤ D ^ (9 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hDN (by norm_num)
      have h2 : ((N : ℝ) / 2) ^ (9 / 10 : ℝ) = N ^ (9 / 10 : ℝ) / 2 ^ (9 / 10 : ℝ) :=
        Real.div_rpow hNpos.le (by norm_num) _
      have h3 : (2 : ℝ) ^ (9 / 10 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (9 / 10 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h4 : (N : ℝ) ^ (9 / 10 : ℝ) / 2 ≤ N ^ (9 / 10 : ℝ) / 2 ^ (9 / 10 : ℝ) :=
        div_le_div_of_nonneg_left hN9 (by positivity) h3
      rw [show (1 - 1 / 10 : ℝ) = 9 / 10 by norm_num]
      linarith
    linarith
  have hD₀ : D₀ ≤ D := by linarith
  -- apply Proposition A.5
  obtain ⟨Msel, hMdisj, hMcov⟩ : ∃ M : Finset ι, (∀ i ∈ M, ∀ j ∈ M, i ≠ j → Disjoint (S i) (S j)) ∧
      ∀ x ∈ A, ∃ i ∈ M, x ∈ S i := by
    refine hA5 D hD₀ α ι A Bs S hdisj hS ?_ ?_ ?_
    · intro x hx
      have := hdegA x hx
      convert this using 4 <;> rfl
    · intro y hy
      have := hdegB y hy
      convert this using 4 <;> rfl
    · intro x y hxy
      have := le_trans (hcodΔ x y hxy) hΔ3
      convert this using 4 <;> rfl
  -- decoding the selection
  have huniq : ∀ i i', i ∈ Msel → i' ∈ Msel → ∀ x, x ∈ S i → x ∈ S i' → i = i' := by
    intro i i' hi hi' x hx hx'
    by_contra hne
    exact Finset.disjoint_left.mp (hMdisj i hi i' hi' hne) hx hx'
  have hcovE : ∀ e : {e // lg e}, ∃ i ∈ Msel, job e.1 ∈ S i :=
    fun e => hMcov _ ((hjobA _).mpr e.2)
  choose ch hchM hchS using hcovE
  have hchjb : ∀ e, jb (ch e) = e.1 := fun e => (hjb _ _).mp (hchS e)
  have hch_inj : ∀ e e' x, x ∈ S (ch e) → x ∈ S (ch e') → e = e' := by
    intro e e' x hx hx'
    have := huniq _ _ (hchM e) (hchM e') x hx hx'
    apply Subtype.ext
    rw [← hchjb e, ← hchjb e', this]
  let ψ : E → Option (𝒞 × Fin Ks × Fin Ks) := fun e =>
    if h : lg e then Sum.elim (fun i : (Σ t, Fin (M₁ t)) => some i.1.2)
      (fun _ : (Σ t, Fin (M₂ t)) => none) (ch ⟨e, h⟩) else none
  -- the chosen option of a colored edge
  have hψsome : ∀ e c i j, ψ e = some (c, i, j) →
      ∃ (h : lg e) (m : Fin (M₁ (e, c, i, j))), ch ⟨e, h⟩ = Sum.inl ⟨(e, c, i, j), m⟩ := by
    intro e c i j hψ
    by_cases h : lg e
    · refine ⟨h, ?_⟩
      have hψ' : Sum.elim (fun i : (Σ t, Fin (M₁ t)) => some i.1.2)
          (fun _ : (Σ t, Fin (M₂ t)) => none) (ch ⟨e, h⟩) = some (c, i, j) := by
        simpa [ψ, h] using hψ
      have hj := hchjb ⟨e, h⟩
      revert hψ' hj
      rcases ch ⟨e, h⟩ with ⟨t, m⟩ | ⟨t, m⟩
      · intro hψ' hj
        simp only [Sum.elim_inl, Option.some.injEq] at hψ'
        change t.1 = e at hj
        obtain ⟨t1, t2⟩ := t
        simp only at hψ' hj
        subst hj; subst hψ'
        exact ⟨m, rfl⟩
      · intro hψ'; simp at hψ'
    · simp [ψ, h] at hψ
  have hψnone : ∀ e (h : lg e), ψ e = none →
      ∃ (t : E × Fin Bmax × Fin Bmax) (m : Fin (M₂ t)), ch ⟨e, h⟩ = Sum.inr ⟨t, m⟩ ∧ t.1 = e := by
    intro e h hψ
    have hψ' : Sum.elim (fun i : (Σ t, Fin (M₁ t)) => some i.1.2)
        (fun _ : (Σ t, Fin (M₂ t)) => none) (ch ⟨e, h⟩) = none := by
      simpa [ψ, h] using hψ
    have hj := hchjb ⟨e, h⟩
    revert hψ' hj
    rcases ch ⟨e, h⟩ with ⟨t, m⟩ | ⟨t, m⟩
    · intro hψ'; simp at hψ'
    · intro _ hj; exact ⟨t, m, rfl, hj⟩
  refine ⟨ψ, ?_, ?_, ?_⟩
  · -- positivity of the chosen options
    intro e c i j hψ
    obtain ⟨h, m, -⟩ := hψsome e c i j hψ
    have hpos : 0 < M₁ (e, c, i, j) := Fin.pos m
    rw [hM₁ (e, c, i, j), if_pos h] at hpos
    have := Nat.floor_pos.mp hpos
    by_contra hle
    push Not at hle
    have : (N : ℝ) * XL e c i j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNpos.le hle
    linarith
  · -- no slot is used twice
    have huse : ∀ e v c i, (∃ j, (src e = v ∧ ψ e = some (c, i, j)) ∨ (tgt e = v ∧ ψ e = some (c, j, i))) →
        ∃ h : lg e, osl v c i ∈ S (ch ⟨e, h⟩) := by
      intro e v c i ⟨j, hj⟩
      rcases hj with ⟨hs, hψ⟩ | ⟨ht, hψ⟩
      · obtain ⟨h, m, hch⟩ := hψsome e c i j hψ
        refine ⟨h, ?_⟩
        rw [hch]
        change osl v c i ∈ S₁ (e, c, i, j)
        rw [m1osl]; exact Or.inl ⟨hs.symm, rfl, rfl⟩
      · obtain ⟨h, m, hch⟩ := hψsome e c j i hψ
        refine ⟨h, ?_⟩
        rw [hch]
        change osl v c i ∈ S₁ (e, c, j, i)
        rw [m1osl]; exact Or.inr ⟨ht.symm, rfl, rfl⟩
    intro e e' v c i h1 h2
    obtain ⟨he, hx⟩ := huse e v c i h1
    obtain ⟨he', hx'⟩ := huse e' v c i h2
    have := hch_inj _ _ _ hx hx'
    exact congrArg Subtype.val this
  · -- the unchosen large edges
    intro v
    have hB0 : 0 < Bmax := lt_of_le_of_lt (Nat.zero_le _) (hBlt v ⟨0, by omega⟩)
    let kk : E → Fin Bmax := fun e => if h : lg e then
      Sum.elim (fun _ : (Σ t, Fin (M₁ t)) => (⟨0, hB0⟩ : Fin Bmax))
        (fun p : (Σ t, Fin (M₂ t)) => if src e = v then p.1.2.1 else p.1.2.2) (ch ⟨e, h⟩)
      else ⟨0, hB0⟩
    set U := (G.inc v).filter (fun e => β ≤ G.w e ∧ ψ e = none) with hU
    have hkk : ∀ e ∈ U, ∃ h : lg e, xsl v (hF e) (kk e) ∈ S (ch ⟨e, h⟩) ∧ (kk e : ℕ) < Bvh v (hF e) := by
      intro e he
      obtain ⟨hev, hlg, hψ⟩ := Finset.mem_filter.mp he
      obtain ⟨t, m, hch, ht1⟩ := hψnone e hlg hψ
      have hval := hM₂pos t (Fin.pos m)
      have hv : v ∈ G.ends e := by simpa [WGraph.inc] using hev
      refine ⟨hlg, ?_⟩
      have hkkt : kk e = if src e = v then t.2.1 else t.2.2 := by
        simp only [kk, hch, Sum.elim_inr]
        exact dif_pos hlg
      rw [hch]
      change xsl v (hF e) (kk e) ∈ S₂ t ∧ _
      obtain ⟨t1, t2, t3⟩ := t
      simp only at ht1 hval hkkt
      subst ht1
      by_cases hs : src t1 = v
      · rw [if_pos hs] at hkkt
        rw [hkkt, m2xsl]
        refine ⟨Or.inl ⟨hs.symm, rfl, rfl⟩, ?_⟩
        rw [← hs]; exact hval.2.1
      · have ht : tgt t1 = v := by
          rcases (hmem t1 v).mp hv with h | h
          · exact absurd h.symm hs
          · exact h.symm
        rw [if_neg hs] at hkkt
        rw [hkkt, m2xsl]
        refine ⟨Or.inr ⟨ht.symm, rfl, rfl⟩, ?_⟩
        rw [← ht]; exact hval.2.2
    -- interval bounds for the weights
    have hhF : ∀ e, lg e → ((hF e : ℕ) : ℝ) ≤ (G.w e - β) / (lam * β) ∧
        (G.w e - β) / (lam * β) < (hF e : ℕ) + 1 := by
      intro e hlg
      have hle : ⌊(G.w e - β) / (lam * β)⌋₊ ≤ Hm := by
        rw [hHm]
        apply Nat.floor_le_floor
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [G.w_le_one e]
      have hfe : (hF e : ℕ) = ⌊(G.w e - β) / (lam * β)⌋₊ := by rw [hhF e]; omega
      rw [hfe]
      have h0 : 0 ≤ (G.w e - β) / (lam * β) := div_nonneg (by linarith [show β ≤ G.w e from hlg]) (by positivity)
      exact ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩
    let u : Fin (Hm + 1) → ℝ := fun h => β + ((h : ℕ) + 1) * lam * β
    have hlamβ : 0 < lam * β := by positivity
    have hw_u : ∀ e, lg e → G.w e ≤ u (hF e) := by
      intro e hlg
      have := (hhF e hlg).2
      rw [div_lt_iff₀ hlamβ] at this
      simp only [u]; nlinarith only [this]
    have hu_w : ∀ e, lg e → u (hF e) ≤ (1 + lam) * G.w e := by
      intro e hlg
      have h1 := (hhF e hlg).1
      rw [le_div_iff₀ hlamβ] at h1
      simp only [u]
      have hh0 : (0 : ℝ) ≤ (hF e : ℕ) := Nat.cast_nonneg _
      have : β ≤ β + ((hF e : ℕ) : ℝ) * lam * β := by
        have : 0 ≤ ((hF e : ℕ) : ℝ) * lam * β := by positivity
        linarith
      nlinarith only [h1, this, hlam0]
    have hu_max : ∀ h, u h ≤ uMax := by
      intro h
      simp only [u]; rw [huMax]
      have : ((h : ℕ) : ℝ) + 1 ≤ Hm + 1 := by
        have : ((h : ℕ) : ℝ) ≤ Hm := by exact_mod_cast Nat.lt_succ_iff.mp h.2
        linarith
      have h2 := mul_le_mul_of_nonneg_right this (mul_pos hlam0 hβ0).le
      linarith
    have hu0 : ∀ h, 0 ≤ u h := fun h => by simp only [u]; positivity
    -- per-interval counting
    have hcardU : ∀ h, ((U.filter (fun e => hF e = h)).card : ℝ) ≤ Bvh v h := by
      intro h
      have hmaps : ∀ e ∈ U.filter (fun e => hF e = h),
          kk e ∈ Finset.univ.filter (fun k : Fin Bmax => (k : ℕ) < Bvh v h) := by
        intro e he
        obtain ⟨he, hh⟩ := Finset.mem_filter.mp he
        obtain ⟨_, -, hlt⟩ := hkk e he
        rw [hh] at hlt
        simp [hlt]
      have hinj : Set.InjOn kk (U.filter (fun e => hF e = h)) := by
        intro e he e' he' hk
        obtain ⟨he, hh⟩ := Finset.mem_filter.mp he
        obtain ⟨he', hh'⟩ := Finset.mem_filter.mp he'
        obtain ⟨h1, hx1, -⟩ := hkk e he
        obtain ⟨h2, hx2, -⟩ := hkk e' he'
        rw [hh, hk] at hx1
        rw [hh'] at hx2
        exact congrArg Subtype.val (hch_inj _ _ _ hx1 hx2)
      have := Finset.card_le_card_of_injOn kk hmaps hinj
      rw [Fin.card_filter_val_lt] at this
      have : (U.filter (fun e => hF e = h)).card ≤ Bvh v h := le_trans this (min_le_right _ _)
      exact_mod_cast this
    have hUh : ∀ h, ∑ e ∈ U.filter (fun e => hF e = h), G.w e ≤ Bvh v h * u h := by
      intro h
      calc ∑ e ∈ U.filter (fun e => hF e = h), G.w e ≤ ∑ e ∈ U.filter (fun e => hF e = h), u h := by
            apply Finset.sum_le_sum
            intro e he
            obtain ⟨he, hh⟩ := Finset.mem_filter.mp he
            rw [← hh]
            exact hw_u e (Finset.mem_filter.mp he).2.1
        _ = (U.filter (fun e => hF e = h)).card * u h := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Bvh v h * u h := mul_le_mul_of_nonneg_right (hcardU h) (hu0 h)
    have hBu : ∀ h, (Bvh v h : ℝ) * u h ≤ (1 + lam) / (1 - lam) *
        ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e * G.w e + (1 + T) * u h := by
      intro h
      have hlam1 : (0 : ℝ) < 1 - lam := by linarith
      have hB : (Bvh v h : ℝ) ≤ Rvh v h / (1 - lam) + 1 + T := by
        rw [hBvh]; push_cast
        have := Nat.ceil_lt_add_one (show 0 ≤ Rvh v h / (1 - lam) by
          apply div_nonneg _ hlam1.le
          rw [hRvh]; exact Finset.sum_nonneg (fun e _ => hrE0 e))
        linarith
      have hRu : Rvh v h * u h ≤ (1 + lam) *
          ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e * G.w e := by
        rw [hRvh, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨-, hlg, hh⟩ := Finset.mem_filter.mp he
        rw [← hh]
        have := hu_w e hlg
        have := hrE0 e
        nlinarith only [this, hu_w e hlg, hrE0 e]
      calc (Bvh v h : ℝ) * u h ≤ (Rvh v h / (1 - lam) + 1 + T) * u h :=
            mul_le_mul_of_nonneg_right hB (hu0 h)
        _ = Rvh v h * u h / (1 - lam) + (1 + T) * u h := by field_simp; ring
        _ ≤ (1 + lam) * (∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e * G.w e) / (1 - lam)
              + (1 + T) * u h := by
            gcongr
        _ = _ := by ring
    -- summing over the intervals
    have hU_split : ∑ e ∈ U, G.w e = ∑ h, ∑ e ∈ U.filter (fun e => hF e = h), G.w e :=
      (Finset.sum_fiberwise U hF G.w).symm
    have hX_split : ∑ e ∈ (G.inc v).filter lg, rE e * G.w e
        = ∑ h, ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e * G.w e := by
      rw [← Finset.sum_fiberwise ((G.inc v).filter lg) hF]
      apply Finset.sum_congr rfl; intro h _
      rw [Finset.filter_filter]
    set X := ∑ e ∈ (G.inc v).filter lg, rE e * G.w e with hXdef
    have hX0 : 0 ≤ X := Finset.sum_nonneg (fun e _ => mul_nonneg (hrE0 e) (G.w_pos e).le)
    have hXn : X ≤ n := by
      calc X ≤ ∑ e ∈ (G.inc v).filter lg, G.w e := by
            apply Finset.sum_le_sum; intro e _
            exact mul_le_of_le_one_left (G.w_pos e).le (hrE1 e)
        _ ≤ ∑ e ∈ G.inc v, G.w e := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun e _ _ => (G.w_pos e).le)
        _ ≤ n := hW v
    have hsumU : ∑ e ∈ U, G.w e ≤ (1 + lam) / (1 - lam) * X + (1 + T) * ((Hm + 1) * uMax) := by
      rw [hU_split, hX_split, Finset.mul_sum]
      have h1 : ∑ h : Fin (Hm + 1), (1 + (T : ℝ)) * u h ≤ (1 + T) * ((Hm + 1) * uMax) := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ h : Fin (Hm + 1), u h ≤ ∑ _h : Fin (Hm + 1), uMax := Finset.sum_le_sum (fun h _ => hu_max h)
          _ = (Hm + 1) * uMax := by simp
      calc ∑ h, ∑ e ∈ U.filter (fun e => hF e = h), G.w e
          ≤ ∑ h, ((1 + lam) / (1 - lam) *
              ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e * G.w e + (1 + T) * u h) :=
            Finset.sum_le_sum (fun h _ => le_trans (hUh h) (hBu h))
        _ = ∑ h, (1 + lam) / (1 - lam) *
              ∑ e ∈ (G.inc v).filter (fun e => lg e ∧ hF e = h), rE e * G.w e
            + ∑ h : Fin (Hm + 1), (1 + (T : ℝ)) * u h := Finset.sum_add_distrib
        _ ≤ _ := by linarith
    -- final arithmetic
    have hlamfrac : (1 + lam) / (1 - lam) * X ≤ X + ε / 2 * n := by
      have hlam1 : (0 : ℝ) < 1 - lam := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hlam1]
      have : 2 * lam * X ≤ ε / 2 * n * (1 - lam) := by
        have h1 : 2 * lam * X ≤ 2 * lam * n := mul_le_mul_of_nonneg_left hXn (by positivity)
        have h2 : 2 * lam * n ≤ ε / 2 * n * (1 - lam) := by
          have : 2 * lam ≤ ε / 2 * (1 - lam) := by nlinarith only [hlamε, hlam8, hε, hlam0]
          nlinarith only [this, hn0]
        linarith
      nlinarith only [this, hX0, hlam0]
    have hT3 : 1 + (T : ℝ) ≤ 3 * n ^ (2 / 3 : ℝ) := by
      have h1 : (T : ℝ) ≤ n ^ (2 / 3 : ℝ) + 1 := by
        rw [hT]; exact (Nat.ceil_lt_add_one (by positivity)).le
      have h2 : 1 ≤ n ^ (2 / 3 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
      linarith
    have huMax0 : 0 ≤ uMax := le_trans (hu0 ⟨0, by omega⟩) (hu_max _)
    have hlast : (1 + (T : ℝ)) * ((Hm + 1) * uMax) ≤ 3 * (Hm + 1) * uMax * n ^ (2 / 3 : ℝ) := by
      have := mul_le_mul_of_nonneg_right hT3 (by positivity : (0 : ℝ) ≤ (Hm + 1) * uMax)
      linarith
    have hgoal : ∑ e ∈ (G.inc v).filter (fun e => β ≤ G.w e),
        G.w e * (1 - ∑ c, ∑ i, ∑ j, XL e c i j) = X := by
      rw [hXdef]; apply Finset.sum_congr rfl; intro e _
      rw [hrEdef, hsEdef]; ring
    rw [hgoal]
    have : ε / 2 * n ≤ ε * n := by nlinarith only [hε, hn0]
    linarith
