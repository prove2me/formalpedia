-- Prove2me | solution 1 for SPFacilityGraph.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:16:02.175833+00:00
-- url     : https://prove2.me/submissions/0c258a0b-c853-4dd2-9667-6bb6f458452c

import Mathlib
import Theorems.Thm_SPFacilityGraph_lemma_I_1
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_triangle
import Definitions.Def_SPFacilityGraph_IsSSPCost
import Definitions.Def_SPFacilityGraph_MetricGraph_embed

set_option autoImplicit false

open SPFacilityGraph

namespace SPFGLocality

/-- concatenation of two chains -/
lemma cat_chain {E : Type*} [NormedAddCommGroup E] (P : E → E → Prop) (m n : ℕ) (p q : ℕ → E)
    (hpq : p m = q 0) (hp : ∀ j < m, P (p j) (p (j+1))) (hq : ∀ j < n, P (q j) (q (j+1))) :
    ∃ r : ℕ → E, r 0 = p 0 ∧ r (m + n) = q n ∧ (∀ j < m + n, P (r j) (r (j+1))) ∧
      ∑ j ∈ Finset.range (m + n), ‖r (j+1) - r j‖ =
        ∑ j ∈ Finset.range m, ‖p (j+1) - p j‖ + ∑ j ∈ Finset.range n, ‖q (j+1) - q j‖ := by
  refine ⟨fun j => if j ≤ m then p j else q (j - m), by simp, ?_, ?_, ?_⟩
  · by_cases h : n = 0
    · subst h; simp [hpq]
    · simp [show ¬ m + n ≤ m by omega]
  · intro j hj
    by_cases h : j + 1 ≤ m
    · have := hp j (by omega)
      simpa [h, show j ≤ m by omega] using this
    · by_cases h' : j = m
      · have := hq 0 (by omega)
        simpa [h', hpq, show j + 1 - j = 1 by omega] using this
      · have := hq (j - m) (by omega)
        simpa [show ¬ j ≤ m by omega, h, show j + 1 - m = j - m + 1 by omega] using this
  · rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      simp [show j ≤ m by omega, show j + 1 ≤ m by omega]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = 0
      · subst h; simp [hpq]
      · simp [show ¬ m + j ≤ m by omega, show ¬ m + j + 1 ≤ m by omega,
          show m + j + 1 - m = j + 1 by omega]

/-- refining every step of a walk into a chain of good steps of the same total length -/
lemma chain_refine {E : Type*} [NormedAddCommGroup E] (P : E → E → Prop) (Q : E → E → Prop)
    (hseg : ∀ a b, P a b → ∃ (N : ℕ) (c : ℕ → E), c 0 = a ∧ c N = b ∧
      (∀ l < N, Q (c l) (c (l+1))) ∧ ∑ l ∈ Finset.range N, ‖c (l+1) - c l‖ = ‖b - a‖)
    (m : ℕ) (p : ℕ → E) (hw : ∀ j < m, P (p j) (p (j+1))) :
    ∃ (N : ℕ) (c : ℕ → E), c 0 = p 0 ∧ c N = p m ∧ (∀ l < N, Q (c l) (c (l+1))) ∧
      ∑ l ∈ Finset.range N, ‖c (l+1) - c l‖ = ∑ j ∈ Finset.range m, ‖p (j+1) - p j‖ := by
  induction m with
  | zero => exact ⟨0, p, rfl, rfl, fun l hl => absurd hl (by omega), by simp⟩
  | succ m ih =>
    obtain ⟨N, c, hc0, hcN, hcQ, hcL⟩ := ih (fun j hj => hw j (by omega))
    obtain ⟨N', d, hd0, hdN, hdQ, hdL⟩ := hseg (p m) (p (m+1)) (hw m (by omega))
    obtain ⟨r, hr0, hrN, hrQ, hrL⟩ := cat_chain Q N N' c d (hcN.trans hd0.symm) hcQ hdQ
    refine ⟨N + N', r, hr0.trans hc0, hrN.trans hdN, hrQ, ?_⟩
    rw [hrL, hcL, hdL, Finset.sum_range_succ]

end SPFGLocality

open SPFGLocality

lemma SPFacilityGraph.MetricGraph.embed_update {k n : ℕ} (G : MetricGraph k) (x : Profile G n)
    (i : Fin n) (w : G.Pt) :
    G.embed (Function.update x i w) = Function.update (G.embed x) i (w : EuclideanSpace ℝ (Fin k)) := by
  funext j
  by_cases h : j = i
  · subst h; simp [MetricGraph.embed]
  · simp [MetricGraph.embed, Function.update_of_ne h]

theorem solution {k n : ℕ} (G : MetricGraph k) (C : Profile G n → G.Pt → ℝ)
    (𝒰 : Finset (Finset ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k))))
    (hcover : ∀ (x : Profile G n) (t : G.Pt), (G.embed x, (t : EuclideanSpace ℝ (Fin k))) ∈
      ⋃ P ∈ 𝒰, convexHull ℝ (P : Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k)))) :
    IsSSPCost G C ↔
      ∀ (i : Fin n) (t : G.Pt) (x : Profile G n) (y z : G.Pt),
        G.dist t z = G.dist t y + G.dist y z →
        (∃ P ∈ 𝒰,
          (G.embed (Function.update x i y), (t : EuclideanSpace ℝ (Fin k))) ∈
            convexHull ℝ (P : Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k))) ∧
          (G.embed (Function.update x i z), (t : EuclideanSpace ℝ (Fin k))) ∈
            convexHull ℝ (P : Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k)))) →
        C (Function.update x i y) t ≤ C (Function.update x i z) t := by
  constructor
  · intro h i t x y z hd _
    exact h i t x y z hd
  intro hloc i t x y z hd
  classical
  let E := EuclideanSpace ℝ (Fin k)
  let V := (Fin n → E) × E
  let Φ : E → V := fun u => (Function.update (G.embed x) i u, (t : E))
  let Adj : E → E → Prop := fun a b => ∃ e ∈ G.edges, a ∈ segment ℝ e.1 e.2 ∧ b ∈ segment ℝ e.1 e.2
  let Q : E → E → Prop := fun a b => Adj a b ∧
    ∃ P ∈ 𝒰, Φ a ∈ convexHull ℝ (P : Set V) ∧ Φ b ∈ convexHull ℝ (P : Set V)
  -- Step 1: every edge step can be subdivided into cell-wise steps
  have hseg : ∀ a b, Adj a b → ∃ (N : ℕ) (c : ℕ → E), c 0 = a ∧ c N = b ∧
      (∀ l < N, Q (c l) (c (l+1))) ∧ ∑ l ∈ Finset.range N, ‖c (l+1) - c l‖ = ‖b - a‖ := by
    rintro a b ⟨e, he, ha, hb⟩
    have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, a + s • (b - a) ∈ segment ℝ e.1 e.2 := fun s hs =>
      (convex_segment e.1 e.2).add_smul_sub_mem ha hb hs
    have hcar : ∀ s ∈ Set.Icc (0:ℝ) 1, a + s • (b - a) ∈ G.carrier := fun s hs =>
      Set.mem_biUnion he (hmem s hs)
    let γ : ℝ → V := fun s => Φ (a + s • (b - a))
    have hγ : ∀ s, γ s = Φ a + s • ((Pi.single i (b - a) : Fin n → E), (0 : E)) := by
      intro s
      refine Prod.ext ?_ ?_
      · show Function.update (G.embed x) i (a + s • (b - a)) =
          Function.update (G.embed x) i a + s • (Pi.single i (b - a) : Fin n → E)
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [Function.update_of_ne h, h]
      · show (t : E) = (t : E) + s • (0 : E)
        simp
    have hcov : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ ⋃ P ∈ 𝒰, convexHull ℝ (P : Set V) := by
      intro s hs
      have := hcover (Function.update x i ⟨a + s • (b - a), hcar s hs⟩) t
      rwa [G.embed_update] at this
    have hcont : ContinuousOn γ (Set.Icc 0 1) := by
      have : γ = fun s => Φ a + s • ((Pi.single i (b - a) : Fin n → E), (0 : E)) := funext hγ
      rw [this]; fun_prop
    have hpw : ∃ (p : ℕ) (r : Fin (p + 1) → ℝ), StrictMono r ∧ r 0 = 0 ∧ r (Fin.last p) = 1 ∧
        ∀ j : Fin p, ∃ a' b' : V, ∀ s ∈ Set.Icc (r j.castSucc) (r j.succ), γ s = a' + s • b' :=
      ⟨1, ![0, 1], by
        refine Fin.strictMono_iff_lt_succ.2 ?_
        intro j; fin_cases j; simp, rfl, rfl,
        fun _ => ⟨_, _, fun s _ => hγ s⟩⟩
    obtain ⟨M, s, hsm, hs0, hs1, hsP⟩ := lemma_I_1 𝒰 γ hcov hcont hpw
    have hsI : ∀ j : Fin (M+1), s j ∈ Set.Icc (0:ℝ) 1 := by
      intro j
      refine ⟨?_, ?_⟩
      · rw [← hs0]; exact hsm.monotone (Fin.zero_le _)
      · rw [← hs1]; exact hsm.monotone (Fin.le_last _)
    let σ : ℕ → ℝ := fun l => if h : l ≤ M then s ⟨l, by omega⟩ else 1
    have hσI : ∀ l, σ l ∈ Set.Icc (0:ℝ) 1 := by
      intro l; by_cases h : l ≤ M
      · simp only [σ, dif_pos h]; exact hsI _
      · simp only [σ, dif_neg h]; exact ⟨zero_le_one, le_rfl⟩
    refine ⟨M, fun l => a + σ l • (b - a), ?_, ?_, ?_, ?_⟩
    · simp [σ, hs0]
    · have : σ M = 1 := by simp only [σ, dif_pos le_rfl]; exact hs1
      simp [this]
    · intro l hl
      refine ⟨⟨e, he, hmem _ (hσI l), hmem _ (hσI (l+1))⟩, ?_⟩
      obtain ⟨P, hP, hsub⟩ := hsP ⟨l, hl⟩
      refine ⟨P, hP, ?_, ?_⟩
      · have h1 : σ l = s (Fin.castSucc ⟨l, hl⟩) := by
          simp only [σ, dif_pos (show l ≤ M by omega)]; rfl
        apply hsub
        exact ⟨σ l, ⟨by rw [h1], by rw [h1]; exact hsm.monotone (Fin.castSucc_le_succ _)⟩, rfl⟩
      · have h1 : σ (l+1) = s (Fin.succ ⟨l, hl⟩) := by
          simp only [σ, dif_pos (show l + 1 ≤ M by omega)]; rfl
        apply hsub
        exact ⟨σ (l+1), ⟨by rw [h1]; exact hsm.monotone (Fin.castSucc_le_succ _), by rw [h1]⟩, rfl⟩
    · have hmono : ∀ l < M, σ l ≤ σ (l+1) := by
        intro l hl
        simp only [σ, dif_pos (show l ≤ M by omega), dif_pos (show l + 1 ≤ M by omega)]
        exact hsm.monotone (by simp [Fin.le_def])
      have : ∀ l ∈ Finset.range M, ‖a + σ (l+1) • (b - a) - (a + σ l • (b - a))‖ =
          (σ (l+1) - σ l) * ‖b - a‖ := by
        intro l hl
        rw [Finset.mem_range] at hl
        rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.2 (hmono l hl))]
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, Finset.sum_range_sub]
      have h0 : σ 0 = 0 := by simp only [σ, dif_pos (Nat.zero_le _)]; exact hs0
      have hM : σ M = 1 := by simp only [σ, dif_pos le_rfl]; exact hs1
      rw [h0, hM]; ring
  -- Step 2: a shortest walk from `y` to `z`, refined into cell-wise steps
  obtain ⟨m, p, hp0, hpm, hpw, hpL⟩ := G.exists_walk_eq_dist y z
  obtain ⟨N, c, hc0, hcN, hcQ, hcL⟩ := chain_refine Adj Q hseg m p hpw
  have hcar : ∀ l ≤ N, c l ∈ G.carrier := by
    intro l hl
    rcases Nat.lt_or_ge l N with h | h
    · obtain ⟨⟨e, he, h1, -⟩, -⟩ := hcQ l h
      exact Set.mem_biUnion he h1
    · have hl' : l = N := le_antisymm hl h
      subst hl'
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · subst h0; rw [hc0, hp0]; exact y.2
      · obtain ⟨⟨e, he, -, h2⟩, -⟩ := hcQ (l - 1) (by omega)
        rw [show l - 1 + 1 = l by omega] at h2
        exact Set.mem_biUnion he h2
  let cp : ℕ → G.Pt := fun l => if h : c l ∈ G.carrier then ⟨c l, h⟩ else t
  have hcp : ∀ l ≤ N, (cp l : E) = c l := by
    intro l hl; simp only [cp, dif_pos (hcar l hl)]
  have hcp0 : cp 0 = y := Subtype.ext (by rw [hcp 0 (Nat.zero_le _), hc0, hp0])
  have hcpN : cp N = z := Subtype.ext (by rw [hcp N le_rfl, hcN, hpm])
  -- Step 3: every refined step is outward
  have hstep_d : ∀ l < N, G.dist (cp l) (cp (l+1)) ≤ ‖c (l+1) - c l‖ := by
    intro l hl
    have := G.dist_le_walk (cp l) (cp (l+1)) 1 (fun j => if j = 0 then c l else c (l+1))
      (by simp [hcp l hl.le]) (by simp [hcp (l+1) hl]) (by
        intro j hj
        have : j = 0 := by omega
        subst this
        obtain ⟨e, he, h1, h2⟩ := (hcQ l hl).1
        exact ⟨e, he, by simpa using h1, by simpa using h2⟩)
    simpa using this
  have hout : ∀ l < N, G.dist t (cp (l+1)) = G.dist t (cp l) + G.dist (cp l) (cp (l+1)) := by
    let f : ℕ → ℝ := fun l => G.dist t (cp l)
    let g : ℕ → ℝ := fun l => f l + G.dist (cp l) (cp (l+1)) - f (l+1)
    let h : ℕ → ℝ := fun l => ‖c (l+1) - c l‖ - G.dist (cp l) (cp (l+1))
    have hg : ∀ l ∈ Finset.range N, 0 ≤ g l := fun l _ => by
      have := G.dist_triangle t (cp l) (cp (l+1)); simp only [g, f]; linarith
    have hh : ∀ l ∈ Finset.range N, 0 ≤ h l := fun l hl => by
      have := hstep_d l (Finset.mem_range.1 hl); simp only [h]; linarith
    have hsum : ∑ l ∈ Finset.range N, (g l + h l) = 0 := by
      have e1 : ∑ l ∈ Finset.range N, (g l + h l) =
          ∑ l ∈ Finset.range N, ‖c (l+1) - c l‖ - ∑ l ∈ Finset.range N, (f (l+1) - f l) := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro l _; simp only [g, h]; ring
      rw [e1, Finset.sum_range_sub, hcL, hpL]
      simp only [f, hcpN, hcp0]; rw [hd]; ring
    intro l hl
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l hl => add_nonneg (hg l hl) (hh l hl))).1 hsum l
      (Finset.mem_range.2 hl)
    have hg0 : g l = 0 := le_antisymm (by linarith [hh l (Finset.mem_range.2 hl)]) (hg l (Finset.mem_range.2 hl))
    simp only [g, f] at hg0; linarith
  -- Step 4: chain the local comparisons
  have hchain : ∀ l ≤ N, C (Function.update x i (cp 0)) t ≤ C (Function.update x i (cp l)) t := by
    intro l
    induction l with
    | zero => intro _; exact le_rfl
    | succ l ih =>
      intro hl
      refine (ih (by omega)).trans (hloc i t x (cp l) (cp (l+1)) (hout l (by omega)) ?_)
      obtain ⟨-, P, hP, h1, h2⟩ := hcQ l (by omega)
      refine ⟨P, hP, ?_, ?_⟩
      · rw [G.embed_update, hcp l (by omega)]; exact h1
      · rw [G.embed_update, hcp (l+1) hl]; exact h2
  have := hchain N le_rfl
  rwa [hcp0, hcpN] at this
