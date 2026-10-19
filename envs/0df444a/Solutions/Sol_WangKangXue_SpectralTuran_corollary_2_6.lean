-- Prove2me | solution 1 for WangKangXue.SpectralTuran.corollary_2_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T12:20:17.453806+00:00
-- url     : https://prove2.me/submissions/eccbd9c5-a1f0-443b-83ac-387285b38dde

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad

set_option autoImplicit false

universe u

open Finset SimpleGraph

-- L1: an (r+1)-colourable F embeds in K_{r+1}(|W|)
theorem wk26_free {W V : Type*} [Fintype W] (F : SimpleGraph W) (G : SimpleGraph V) (r : ℕ)
    (hcol : F.Colorable (r + 1)) (hF : F.Free G) :
    ¬ completeEquipartiteGraph (r + 1) (Fintype.card W) ⊑ G := by
  intro h
  obtain ⟨C⟩ := hcol
  apply hF
  refine (isContained_completeEquipartiteGraph_of_colorable C _ (fun c => ?_)).trans h
  exact Fintype.card_le_of_injective _ Subtype.val_injective

-- ordered adjacent pairs inside U (= 2 e(G[U]))
def wk26S {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : ℕ :=
  ∑ v ∈ U, #{w ∈ U | G.Adj v w}

theorem wk26S_le {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    wk26S G U ≤ #U * #U := by
  unfold wk26S
  calc ∑ v ∈ U, #{w ∈ U | G.Adj v w} ≤ ∑ _v ∈ U, #U :=
        Finset.sum_le_sum (fun v _ => Finset.card_filter_le _ _)
    _ = #U * #U := by rw [Finset.sum_const, smul_eq_mul]

theorem wk26S_erase {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) (hv : v ∈ U) :
    wk26S G U = wk26S G (U.erase v) + 2 * #{w ∈ U | G.Adj v w} := by
  have h1 : ∀ x ∈ U.erase v, #{w ∈ U | G.Adj x w} =
      #{w ∈ U.erase v | G.Adj x w} + (if G.Adj x v then 1 else 0) := by
    intro x _
    rw [Finset.filter_erase]
    split_ifs with h
    · rw [Finset.card_erase_add_one]
      simp [hv, h]
    · rw [Finset.erase_eq_of_notMem]
      · simp
      · simp [h]
  have h2 : ∑ x ∈ U.erase v, (if G.Adj x v then 1 else 0) = #{w ∈ U | G.Adj v w} := by
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hx⟩, hadj⟩
      exact ⟨hx, hadj.symm⟩
    · rintro ⟨hx, hadj⟩
      exact ⟨⟨G.ne_of_adj hadj |>.symm, hx⟩, hadj.symm⟩
  unfold wk26S
  rw [← Finset.add_sum_erase U _ hv, Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]
  ring

-- L3: iterative deletion of low-degree vertices
theorem wk26_del {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a R : ℝ) (ha : a ≤ 1) (U₀ : Finset V) :
    ∀ (k : ℕ) (U : Finset V), #U = k → U ⊆ U₀ →
      a * (#U : ℝ) ^ 2 + R - ((#U₀ : ℝ) - #U) ≤ wk26S G U →
      ∃ U' ⊆ U, a * (#U' : ℝ) ^ 2 + R - ((#U₀ : ℝ) - #U') ≤ wk26S G U' ∧
        ∀ v ∈ U', a * #U' ≤ #{w ∈ U' | G.Adj v w} := by
  intro k
  induction k with
  | zero =>
    intro U hU _ h
    refine ⟨U, subset_refl _, h, ?_⟩
    intro v hv
    rw [Finset.card_eq_zero.mp hU] at hv
    simp at hv
  | succ k ih =>
    intro U hU hsub h
    by_cases hall : ∀ v ∈ U, a * #U ≤ #{w ∈ U | G.Adj v w}
    · exact ⟨U, subset_refl _, h, hall⟩
    · push Not at hall
      obtain ⟨v, hv, hlt⟩ := hall
      have hE := wk26S_erase G U v hv
      have hEr : (wk26S G U : ℝ) = wk26S G (U.erase v) + 2 * #{w ∈ U | G.Adj v w} := by
        exact_mod_cast hE
      have hc1 : #(U.erase v) + 1 = #U := Finset.card_erase_add_one hv
      have hc : #(U.erase v) = k := by omega
      have hcr : (#(U.erase v) : ℝ) + 1 = #U := by exact_mod_cast hc1
      obtain ⟨U', hU's, h1, h2⟩ := ih (U.erase v) hc ((Finset.erase_subset _ _).trans hsub) (by
        have hx : a * ((#U : ℝ) - 1) ^ 2 = a * (#U : ℝ) ^ 2 - 2 * (a * #U) + a := by ring
        have he : (#(U.erase v) : ℝ) = #U - 1 := by linarith
        rw [he, hx]
        linarith)
      exact ⟨U', hU's.trans (Finset.erase_subset _ _), h1, h2⟩

-- L2: Erdos-Stone (min-degree form) for a vertex subset of any finite type
theorem wk26_esmin {ε : ℝ} (hε : 0 < ε) (r T : ℕ) : ∃ N : ℕ, ∀ {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V), N ≤ #U →
    (∀ v ∈ U, (1 - 1 / (r : ℝ) + ε) * #U ≤ #{w ∈ U | G.Adj v w}) →
    completeEquipartiteGraph (r + 1) T ⊑ G := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_completeEquipartiteGraph_isContained_of_minDegree hε r T)
  refine ⟨N, fun {V} _ _ G _ U hU hdeg => ?_⟩
  let e : Fin #U ≃ U := (U.equivFin).symm
  let G' : SimpleGraph (Fin #U) := G.comap (fun i => ((e i : U) : V))
  have hcopy : G' ⊑ G := ⟨⟨⟨fun i => (e i : V), fun h => h⟩,
    fun i j h => e.injective (Subtype.ext h)⟩⟩
  have hdeg' : ∀ i, (G'.degree i : ℝ) = #{w ∈ U | G.Adj (e i) w} := by
    intro i
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    norm_cast
    refine Finset.card_bij (fun j _ => (e j : V)) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨(e j).2, hj⟩
    · intro a _ b _ h
      exact e.injective (Subtype.ext h)
    · intro w hw
      simp only [Finset.mem_filter] at hw
      refine ⟨e.symm ⟨w, hw.1⟩, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change G.Adj (e i : V) (e (e.symm ⟨w, hw.1⟩) : V)
      simpa using hw.2
  have hmin : (G'.minDegree : ℝ) ≥ (1 - 1 / (r : ℝ) + ε) * #U := by
    rcases Nat.eq_zero_or_pos #U with h0 | hpos
    · have h0' : ((#U : ℕ) : ℝ) = 0 := by exact_mod_cast h0
      rw [h0', mul_zero]; positivity
    · have : Nonempty (Fin #U) := ⟨⟨0, hpos⟩⟩
      obtain ⟨i, hi⟩ := G'.exists_minimal_degree_vertex
      rw [hi, hdeg' i]
      exact hdeg _ (e i).2
  exact (hN #U hU hmin).trans hcopy

-- L4: Erdos-Stone (edge form)
theorem wk26_ese {r t : ℕ} (hr : 1 ≤ r) {b : ℝ} (hb : 0 < b) : ∃ N : ℕ, ∀ {V : Type u}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ¬ completeEquipartiteGraph (r + 1) t ⊑ G →
    ∀ U : Finset V, N ≤ #U → (wk26S G U : ℝ) ≤ (1 - 1 / (r : ℝ) + b) * (#U : ℝ) ^ 2 := by
  obtain ⟨N₁, hN₁⟩ := wk26_esmin (ε := b / 2) (by linarith) r t
  refine ⟨N₁ + ⌈4 * ((N₁ : ℝ) + 1) / b⌉₊ + 1, ?_⟩
  intro V _ _ G _ hfree U hU
  have hSle : (wk26S G U : ℝ) ≤ (#U : ℝ) ^ 2 := by
    have := wk26S_le G U
    rw [sq]; exact_mod_cast this
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hinv : 0 < 1 / (r : ℝ) := by positivity
  have hinv1 : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hr'
  by_cases htriv : 1 ≤ 1 - 1 / (r : ℝ) + b
  · nlinarith [sq_nonneg (#U : ℝ)]
  push Not at htriv
  by_contra hlt
  push Not at hlt
  set k := #U with hk
  set a : ℝ := 1 - 1 / (r : ℝ) + b / 2 with ha
  have ha1 : a ≤ 1 := by linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨U', _, h1, h2⟩ := wk26_del G a (b / 2 * (k : ℝ) ^ 2) ha1 U k U rfl (subset_refl _)
    (by simp only [sub_self, sub_zero]; nlinarith)
  have hS' : (wk26S G U' : ℝ) ≤ (#U' : ℝ) ^ 2 := by
    have := wk26S_le G U'
    rw [sq]; exact_mod_cast this
  have hkU' : (#U' : ℝ) ≤ k := by exact_mod_cast Finset.card_le_card ‹U' ⊆ U›
  have hbig : b / 4 * (k : ℝ) ^ 2 ≤ (#U' : ℝ) ^ 2 := by
    have hk1 : 4 * ((N₁ : ℝ) + 1) / b ≤ k := by
      have := Nat.le_ceil (4 * ((N₁ : ℝ) + 1) / b)
      have : (⌈4 * ((N₁ : ℝ) + 1) / b⌉₊ : ℝ) ≤ k := by
        have : ⌈4 * ((N₁ : ℝ) + 1) / b⌉₊ ≤ k := by omega
        exact_mod_cast this
      linarith
    have hk2 : 4 ≤ b * k := by
      rw [div_le_iff₀ hb] at hk1
      nlinarith
    have : (k : ℝ) ≤ b / 4 * (k : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (#U' : ℝ)]
  have hN' : N₁ ≤ #U' := by
    by_contra hc
    push Not at hc
    have hc' : (#U' : ℝ) + 1 ≤ N₁ := by exact_mod_cast hc
    have hk1 : 4 * ((N₁ : ℝ) + 1) / b ≤ k := by
      have := Nat.le_ceil (4 * ((N₁ : ℝ) + 1) / b)
      have : (⌈4 * ((N₁ : ℝ) + 1) / b⌉₊ : ℝ) ≤ k := by
        have : ⌈4 * ((N₁ : ℝ) + 1) / b⌉₊ ≤ k := by omega
        exact_mod_cast this
      linarith
    have hk3 : 4 * ((N₁ : ℝ) + 1) ≤ b * k := by
      rw [div_le_iff₀ hb] at hk1; linarith
    have hkN : (N₁ : ℝ) ≤ k := by
      have : N₁ ≤ k := by omega
      exact_mod_cast this
    have hU'0 : (0 : ℝ) ≤ #U' := by positivity
    nlinarith
  exact hfree (hN₁ G U' hN' h2)

-- blow-up: each vertex replaced by L copies; K_R(t)-free G gives K_R(tL)-free blow-up
theorem wk26_blowfree {V : Type*} (G : SimpleGraph V) (R t L : ℕ) (hL : 0 < L)
    (h : ¬ completeEquipartiteGraph R t ⊑ G) :
    ¬ completeEquipartiteGraph R (t * L) ⊑ G.comap (Prod.fst : V × Fin L → V) := by
  classical
  rintro ⟨f⟩
  apply h
  have hP : ∀ i : Fin R,
      t ≤ #((univ : Finset (Fin (t * L))).image (fun j => (f (i, j)).1)) := by
    intro i
    have hc := Finset.card_le_mul_card_image (f := fun j => (f (i, j)).1)
      (univ : Finset (Fin (t * L))) L (by
        intro a _
        calc #{j ∈ (univ : Finset (Fin (t * L))) | (f (i, j)).1 = a}
            ≤ #(univ : Finset (Fin L)) := by
              apply Finset.card_le_card_of_injOn (fun j => (f (i, j)).2)
              · intro j _; simp
              · intro j₁ hj₁ j₂ hj₂ heq
                simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hj₁ hj₂
                have h12 : f (i, j₁) = f (i, j₂) := Prod.ext (hj₁.trans hj₂.symm) heq
                have := f.injective h12
                exact (Prod.mk.inj this).2
          _ = L := by simp)
    simp only [card_univ, Fintype.card_fin] at hc
    by_contra hlt
    push Not at hlt
    have : L * #((univ : Finset (Fin (t * L))).image (fun j => (f (i, j)).1)) < L * t :=
      Nat.mul_lt_mul_of_pos_left hlt hL
    rw [mul_comm L t] at this
    omega
  have hemb : ∀ i : Fin R,
      Nonempty (Fin t ↪ ((univ : Finset (Fin (t * L))).image (fun j => (f (i, j)).1))) := by
    intro i
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, Fintype.card_coe]
    exact hP i
  let g : Fin R × Fin t → V := fun p => ((Classical.choice (hemb p.1)) p.2 : V)
  have hmem : ∀ p : Fin R × Fin t, ∃ j, (f (p.1, j)).1 = g p := by
    intro p
    have := ((Classical.choice (hemb p.1)) p.2).2
    rw [Finset.mem_image] at this
    obtain ⟨j, _, hj⟩ := this
    exact ⟨j, hj⟩
  have hadj : ∀ p q : Fin R × Fin t, p.1 ≠ q.1 → G.Adj (g p) (g q) := by
    intro p q hpq
    obtain ⟨j, hj⟩ := hmem p
    obtain ⟨j', hj'⟩ := hmem q
    have := f.toHom.map_adj
      (show (completeEquipartiteGraph R (t * L)).Adj (p.1, j) (q.1, j') from hpq)
    rw [← hj, ← hj']
    exact this
  refine ⟨⟨⟨g, fun {p q} hpq => hadj p q hpq⟩, ?_⟩⟩
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only at h1
    subst h1
    have : (Classical.choice (hemb p1)) p2 = (Classical.choice (hemb p1)) q2 := Subtype.ext hpq
    rw [(Classical.choice (hemb p1)).injective this]
  · exact absurd hpq (hadj p q h1).ne

theorem wk26_sumUB {V : Type*} [Fintype V] (L : ℕ) (m : V → ℕ) (hm : ∀ u, m u ≤ L)
    (g : V → ℕ) :
    ∑ p ∈ (univ : Finset (V × Fin L)).filter (fun p => (p.2 : ℕ) < m p.1), g p.1 =
      ∑ u, m u * g u := by
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, smul_eq_mul, Fin.card_filter_val_lt,
    min_eq_right (hm u)]

-- L5: spectral radius vs edges for K_{r+1}(t)-free graphs (blow-up + Erdos-Stone)
theorem wk26_spec {r t : ℕ} (hr : 1 ≤ r) {β : ℝ} (hβ : 0 < β) : ∃ N : ℕ, ∀ {V : Type u}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ¬ completeEquipartiteGraph (r + 1) t ⊑ G → N ≤ Fintype.card V →
    ∀ (x : V → ℝ) (lam : ℝ), ∑ u, x u ^ 2 = 1 → (Fintype.card V : ℝ) / 4 ≤ lam →
    (∀ u, lam * x u = ∑ v ∈ univ.filter (G.Adj u), x v) →
    lam ^ 2 ≤ (1 - 1 / (r : ℝ) + β) * wk26S G univ := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌈6 / β⌉₊ + 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = 16 * M := ⟨_, rfl⟩
  obtain ⟨N₄, hN₄⟩ := wk26_ese (r := r) (t := t * L) hr (b := β / 2) (by linarith)
  refine ⟨N₄ + 1, ?_⟩
  intro V _ _ G _ hfree hN x lam hx hlam heig
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card V := ⟨_, rfl⟩
  rw [← hn] at hN hlam
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlam0 : 0 < lam := by linarith
  have hM2 : 2 ≤ M := by omega
  have hMr : (6 : ℝ) ≤ β * M := by
    have h1 := Nat.le_ceil (6 / β)
    have h2 : ((⌈6 / β⌉₊ : ℕ) : ℝ) ≤ M := by
      have : ⌈6 / β⌉₊ ≤ M := by omega
      exact_mod_cast this
    have h3 : 6 / β ≤ M := h1.trans h2
    rw [div_le_iff₀ hβ] at h3
    linarith
  have hMpos : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hLpos : 0 < L := by omega
  -- step a: entries are spread
  have habs : (∑ v, |x v|) ^ 2 ≤ n := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset V) (fun _ => (1 : ℝ)) (fun v => |x v|)
    simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, sq_abs] at this
    rw [hx, mul_one, ← hn] at this
    exact this
  have hy : ∀ u, x u ^ 2 * n ≤ 16 := by
    intro u
    have h1 : lam * |x u| ≤ ∑ v, |x v| := by
      have : |lam * x u| ≤ ∑ v ∈ univ.filter (G.Adj u), |x v| := by
        rw [heig u]; exact Finset.abs_sum_le_sum_abs _ _
      rw [abs_mul, abs_of_pos hlam0] at this
      exact this.trans (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => abs_nonneg _))
    have h2 : (lam * |x u|) ^ 2 ≤ n := (pow_le_pow_left₀ (by positivity) h1 2).trans habs
    rw [mul_pow, sq_abs] at h2
    have h3 : (n : ℝ) ^ 2 / 16 ≤ lam ^ 2 := by nlinarith
    have h4 : x u ^ 2 * ((n : ℝ) ^ 2 / 16) ≤ n := by
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (x u))
      linarith
    nlinarith [sq_nonneg (x u)]
  -- step b: Cauchy-Schwarz
  set Nb : V → Finset V := fun u => univ.filter (G.Adj u) with hNb
  have hlam_eq : lam = ∑ u, ∑ v ∈ Nb u, x u * x v := by
    calc lam = lam * ∑ u, x u ^ 2 := by rw [hx, mul_one]
      _ = ∑ u, x u * (lam * x u) := by
          rw [mul_sum]; exact sum_congr rfl (fun u _ => by ring)
      _ = _ := by
          refine sum_congr rfl (fun u _ => ?_)
          rw [heig u, mul_sum]
  have hCS : lam ^ 2 ≤ (wk26S G univ : ℝ) * ∑ u, ∑ v ∈ Nb u, x u ^ 2 * x v ^ 2 := by
    have hA : lam ≤ ∑ u, ∑ v ∈ Nb u, |x u| * |x v| := by
      rw [hlam_eq]
      refine sum_le_sum (fun u _ => sum_le_sum (fun v _ => ?_))
      rw [← abs_mul]; exact le_abs_self _
    have e1 : ∑ u, ∑ v ∈ Nb u, |x u| * |x v| =
        ∑ p ∈ univ.sigma Nb, |x p.1| * |x p.2| :=
      (Finset.sum_sigma univ Nb (fun p : (_ : V) × V => |x p.1| * |x p.2|)).symm
    have e2 : ∑ u, ∑ v ∈ Nb u, x u ^ 2 * x v ^ 2 =
        ∑ p ∈ univ.sigma Nb, x p.1 ^ 2 * x p.2 ^ 2 :=
      (Finset.sum_sigma univ Nb (fun p : (_ : V) × V => x p.1 ^ 2 * x p.2 ^ 2)).symm
    have e3 : (wk26S G univ : ℝ) = ∑ p ∈ univ.sigma Nb, (1 : ℝ) ^ 2 := by
      simp only [one_pow, sum_const, card_sigma, nsmul_eq_mul, mul_one]
      unfold wk26S
      push_cast
      rfl
    have cs := sum_mul_sq_le_sq_mul_sq (univ.sigma Nb) (fun _ => (1 : ℝ))
      (fun p => |x p.1| * |x p.2|)
    simp only [one_mul, mul_pow, sq_abs] at cs
    rw [e1] at hA
    rw [e2, e3]
    simp only [one_pow] at cs ⊢
    exact (pow_le_pow_left₀ hlam0.le hA 2).trans cs
  -- step c: the weighted edge density is at most c + β (blow-up)
  have hQ : ∑ u, ∑ v ∈ Nb u, x u ^ 2 * x v ^ 2 ≤ 1 - 1 / (r : ℝ) + β := by
    set m : V → ℕ := fun u => ⌊x u ^ 2 * n * M⌋₊ with hm
    have hm_le : ∀ u, (m u : ℝ) ≤ x u ^ 2 * n * M := fun u => Nat.floor_le (by positivity)
    have hm_lt : ∀ u, x u ^ 2 * n * M < m u + 1 := fun u => Nat.lt_floor_add_one _
    have hmL : ∀ u, m u ≤ L := by
      intro u
      have : (m u : ℝ) ≤ L := by
        calc (m u : ℝ) ≤ x u ^ 2 * n * M := hm_le u
          _ ≤ 16 * M := by nlinarith [hy u]
          _ = L := by rw [hL]; push_cast; ring
      exact_mod_cast this
    have hsum := wk26_sumUB L m hmL
    set UB : Finset (V × Fin L) := (univ : Finset (V × Fin L)).filter
      (fun p => (p.2 : ℕ) < m p.1) with hUB
    have hcardUB : #UB = ∑ u, m u := by
      rw [Finset.card_eq_sum_ones, hsum (fun _ => 1)]
      simp
    have hSB : wk26S (G.comap (Prod.fst : V × Fin L → V)) UB = ∑ u, m u * ∑ v ∈ Nb u, m v := by
      unfold wk26S
      have hin : ∀ p : V × Fin L, #{q ∈ UB | (G.comap (Prod.fst : V × Fin L → V)).Adj p q} =
          ∑ v ∈ Nb p.1, m v := by
        intro p
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        have := hsum (fun v => if G.Adj p.1 v then 1 else 0)
        simp only [comap_adj] at this ⊢
        rw [this, hNb, Finset.sum_filter]
        refine sum_congr rfl (fun v _ => ?_)
        split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun p _ => hin p)]
      exact hsum (fun u => ∑ v ∈ Nb u, m v)
    have hfreeB := wk26_blowfree G (r + 1) t L hLpos hfree
    have hsumm : (∑ u, (m u : ℝ)) ≤ n * M := by
      calc (∑ u, (m u : ℝ)) ≤ ∑ u, x u ^ 2 * n * M := sum_le_sum (fun u _ => hm_le u)
        _ = n * M := by rw [← sum_mul, ← sum_mul, hx]; ring
    have hsumm2 : (n : ℝ) * M - n ≤ ∑ u, (m u : ℝ) := by
      calc (n : ℝ) * M - n = ∑ u, (x u ^ 2 * n * M - 1) := by
            rw [sum_sub_distrib, ← sum_mul, ← sum_mul, hx]; simp [hn]
        _ ≤ ∑ u, (m u : ℝ) := sum_le_sum (fun u _ => by linarith [hm_lt u])
    have hUBbig : N₄ ≤ #UB := by
      have : (N₄ : ℝ) ≤ #UB := by
        rw [hcardUB]; push_cast
        have : (N₄ : ℝ) + 1 ≤ n := by exact_mod_cast hN
        nlinarith
      exact_mod_cast this
    have hES := hN₄ (G.comap (Prod.fst : V × Fin L → V)) hfreeB UB hUBbig
    rw [hSB, hcardUB] at hES
    push_cast at hES
    have hc0 : 0 ≤ 1 - 1 / (r : ℝ) + β / 2 := by
      have : 1 / (r : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast hr
      linarith
    have hES2 : (∑ u, (m u : ℝ) * ∑ v ∈ Nb u, (m v : ℝ)) ≤
        (1 - 1 / (r : ℝ) + β / 2) * ((n : ℝ) * M) ^ 2 := by
      refine hES.trans (mul_le_mul_of_nonneg_left ?_ hc0)
      exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hsumm 2
    -- compare weights with the integer parts
    have hcmp : (∑ u, ∑ v ∈ Nb u, x u ^ 2 * x v ^ 2) * ((n : ℝ) * M) ^ 2 ≤
        (∑ u, (m u : ℝ) * ∑ v ∈ Nb u, (m v : ℝ)) + 2 * n * (n * M) + (n : ℝ) ^ 2 := by
      have step1 : (∑ u, ∑ v ∈ Nb u, x u ^ 2 * x v ^ 2) * ((n : ℝ) * M) ^ 2 ≤
          ∑ u, ∑ v ∈ Nb u, ((m u : ℝ) + 1) * ((m v : ℝ) + 1) := by
        rw [sum_mul]
        refine sum_le_sum (fun u _ => ?_)
        rw [sum_mul]
        refine sum_le_sum (fun v _ => ?_)
        have hu := hm_lt u
        have hv := hm_lt v
        have : x u ^ 2 * x v ^ 2 * ((n : ℝ) * M) ^ 2 = (x u ^ 2 * n * M) * (x v ^ 2 * n * M) := by
          ring
        rw [this]
        exact mul_le_mul hu.le hv.le (by positivity) (by positivity)
      have step2 : ∑ u, ∑ v ∈ Nb u, ((m u : ℝ) + 1) * ((m v : ℝ) + 1) ≤
          (∑ u, (m u : ℝ) * ∑ v ∈ Nb u, (m v : ℝ)) + ∑ u, ∑ v : V, ((m u : ℝ) + m v + 1) := by
        rw [← sum_add_distrib]
        refine sum_le_sum (fun u _ => ?_)
        rw [mul_sum]
        have : ∑ v ∈ Nb u, ((m u : ℝ) + 1) * ((m v : ℝ) + 1) =
            ∑ v ∈ Nb u, (m u : ℝ) * m v + ∑ v ∈ Nb u, ((m u : ℝ) + m v + 1) := by
          rw [← sum_add_distrib]; exact sum_congr rfl (fun v _ => by ring)
        rw [this]
        have : ∑ v ∈ Nb u, ((m u : ℝ) + m v + 1) ≤ ∑ v : V, ((m u : ℝ) + m v + 1) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
        linarith
      have step3 : ∑ u, ∑ v : V, ((m u : ℝ) + m v + 1) = 2 * n * ∑ u, (m u : ℝ) + (n : ℝ) ^ 2 := by
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← hn, ← mul_sum]
        ring
      have : 2 * (n : ℝ) * ∑ u, (m u : ℝ) ≤ 2 * n * (n * M) := by
        have := mul_le_mul_of_nonneg_left hsumm (by positivity : (0 : ℝ) ≤ 2 * n)
        linarith
      linarith
    have hfin : (∑ u, ∑ v ∈ Nb u, x u ^ 2 * x v ^ 2) * ((n : ℝ) * M) ^ 2 ≤
        (1 - 1 / (r : ℝ) + β) * ((n : ℝ) * M) ^ 2 := by
      have h1 : 2 * (n : ℝ) * (n * M) + (n : ℝ) ^ 2 ≤ β / 2 * ((n : ℝ) * M) ^ 2 := by
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        have : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * M := by nlinarith
        have : β / 2 * ((n : ℝ) * M) ^ 2 = (β * M) / 2 * ((n : ℝ) ^ 2 * M) := by ring
        rw [this]
        nlinarith
      nlinarith
    have hpos : 0 < ((n : ℝ) * M) ^ 2 := by positivity
    exact le_of_mul_le_mul_right hfin hpos
  calc lam ^ 2 ≤ (wk26S G univ : ℝ) * ∑ u, ∑ v ∈ Nb u, x u ^ 2 * x v ^ 2 := hCS
    _ ≤ (wk26S G univ : ℝ) * (1 - 1 / (r : ℝ) + β) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = _ := by ring

-- build a copy of K_R(t) from R pairwise completely joined classes of size >= t
theorem wk26_mkcopy {V : Type*} (G : SimpleGraph V) (R t : ℕ) (C : Fin R → Finset V)
    (hC : ∀ i, t ≤ #(C i)) (hadj : ∀ i i', i ≠ i' → ∀ a ∈ C i, ∀ b ∈ C i', G.Adj a b) :
    completeEquipartiteGraph R t ⊑ G := by
  classical
  have hemb : ∀ i, Nonempty (Fin t ↪ C i) := fun i =>
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, Fintype.card_coe]; exact hC i)
  let g : Fin R × Fin t → V := fun p => ((Classical.choice (hemb p.1)) p.2 : V)
  have hg : ∀ p, g p ∈ C p.1 := fun p => ((Classical.choice (hemb p.1)) p.2).2
  have hadj' : ∀ p q : Fin R × Fin t, p.1 ≠ q.1 → G.Adj (g p) (g q) :=
    fun p q h => hadj _ _ h _ (hg p) _ (hg q)
  refine ⟨⟨⟨g, fun {p q} hpq => hadj' p q hpq⟩, ?_⟩⟩
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only at h1
    subst h1
    have : (Classical.choice (hemb p1)) p2 = (Classical.choice (hemb p1)) q2 := Subtype.ext hpq
    rw [(Classical.choice (hemb p1)).injective this]
  · exact absurd hpq (hadj' p q h1).ne

def wk26part {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r T : ℕ}
    (f : Copy (completeEquipartiteGraph r T) G) (i : Fin r) : Finset V :=
  univ.image (fun j => f (i, j))

theorem wk26part_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r T : ℕ}
    (f : Copy (completeEquipartiteGraph r T) G) (i : Fin r) : #(wk26part f i) = T := by
  unfold wk26part
  rw [Finset.card_image_of_injective, card_univ, Fintype.card_fin]
  intro j j' h
  exact (Prod.mk.inj (f.injective h)).2

theorem wk26part_adj {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r T : ℕ}
    (f : Copy (completeEquipartiteGraph r T) G) {i i' : Fin r} (h : i ≠ i') {a b : V}
    (ha : a ∈ wk26part f i) (hb : b ∈ wk26part f i') : G.Adj a b := by
  unfold wk26part at ha hb
  rw [Finset.mem_image] at ha hb
  obtain ⟨j, _, rfl⟩ := ha
  obtain ⟨j', _, rfl⟩ := hb
  exact f.toHom.map_adj (show (completeEquipartiteGraph r T).Adj (i, j) (i', j') from h)

theorem wk26part_sub {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r T : ℕ}
    (f : Copy (completeEquipartiteGraph r T) G) (U : Finset V) (hfU : ∀ p, f p ∈ U) (i : Fin r) :
    wk26part f i ⊆ U := by
  intro a ha
  unfold wk26part at ha
  rw [Finset.mem_image] at ha
  obtain ⟨j, _, rfl⟩ := ha
  exact hfU _

theorem wk26_filtercount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {r T t : ℕ} (ht : 1 ≤ t) (htT : t ≤ T)
    (f : Copy (completeEquipartiteGraph r T) G)
    (hfree : ¬ completeEquipartiteGraph (r + 1) t ⊑ G) (Fl : Finset V)
    (hFl : ∀ w ∈ Fl, ∀ i, t ≤ #{u ∈ wk26part f i | G.Adj w u}) :
    #Fl < (T.choose t) ^ r * t := by
  by_contra hge
  push Not at hge
  have hex : ∀ w ∈ Fl, ∀ i, ∃ y ⊆ {u ∈ wk26part f i | G.Adj w u}, #y = t :=
    fun w hw i => Finset.exists_subset_card_eq (hFl w hw i)
  choose! σ hσ1 hσ2 using hex
  have hmaps : ∀ w ∈ Fl, σ w ∈ Fintype.piFinset (fun i : Fin r => (wk26part f i).powersetCard t) := by
    intro w hw
    rw [Fintype.mem_piFinset]
    intro i
    rw [mem_powersetCard]
    exact ⟨(hσ1 w hw i).trans (filter_subset _ _), hσ2 w hw i⟩
  have hcard : #(Fintype.piFinset (fun i : Fin r => (wk26part f i).powersetCard t)) =
      (T.choose t) ^ r := by
    rw [Fintype.card_piFinset]
    simp [card_powersetCard, wk26part_card]
  have hpos : 0 < (T.choose t) ^ r := pow_pos (Nat.choose_pos htT) _
  obtain ⟨y, hy, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (n := t - 1) (by
      rw [hcard]
      calc (T.choose t) ^ r * (t - 1) < (T.choose t) ^ r * t :=
            Nat.mul_lt_mul_of_pos_left (by omega) hpos
        _ ≤ #Fl := hge)
  rw [Fintype.mem_piFinset] at hy
  apply hfree
  refine wk26_mkcopy G (r + 1) t (Fin.lastCases ({w ∈ Fl | σ w = y}) y) ?_ ?_
  · intro i
    induction i using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; omega
    | cast i => rw [Fin.lastCases_castSucc]; exact (mem_powersetCard.mp (hy i)).2.ge
  · intro i i' hii' a ha b hb
    induction i using Fin.lastCases with
    | last =>
      induction i' using Fin.lastCases with
      | last => exact absurd rfl hii'
      | cast j =>
        rw [Fin.lastCases_last, mem_filter] at ha
        rw [Fin.lastCases_castSucc] at hb
        rw [← ha.2] at hb
        exact (mem_filter.mp ((hσ1 a ha.1 j) hb)).2
    | cast j =>
      induction i' using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last, mem_filter] at hb
        rw [Fin.lastCases_castSucc] at ha
        rw [← hb.2] at ha
        exact ((mem_filter.mp ((hσ1 b hb.1 j) ha)).2).symm
      | cast j' =>
        rw [Fin.lastCases_castSucc] at ha hb
        have hjj : j ≠ j' := fun h => hii' (by rw [h])
        exact wk26part_adj f hjj ((mem_powersetCard.mp (hy j)).1 ha)
          ((mem_powersetCard.mp (hy j')).1 hb)

theorem wk26_dc {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (P U : Finset V) :
    ∑ w ∈ U, #{u ∈ P | G.Adj w u} = ∑ u ∈ P, #{w ∈ U | G.Adj u w} := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun w _ => ?_))
  simp only [G.adj_comm w u]

-- structural core: given a K_r(T) inside a min-degree set U, classify vertices
theorem wk26_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {r t T s : ℕ} (hr : 1 ≤ r) (ht : 1 ≤ t) (hT : 2 * t * s + t ≤ T)
    (hfree : ¬ completeEquipartiteGraph (r + 1) t ⊑ G) (U : Finset V) (α : ℝ)
    (hdeg : ∀ v ∈ U, (1 - 1 / (r : ℝ) - α) * #U ≤ #{w ∈ U | G.Adj v w})
    (f : Copy (completeEquipartiteGraph r T) G) (hfU : ∀ p, f p ∈ U) :
    ∃ (P : V → Fin r) (Gd : Finset V), Gd ⊆ U ∧
      (#(U \ Gd) : ℝ) ≤ (T.choose t) ^ r * t +
        (t * #U + (T.choose t) ^ r * t * (r * T) + r * T * α * #U) / (s + 1) ∧
      ∀ i : Fin r, ∀ A B : Finset V, A ⊆ Gd → B ⊆ Gd → (∀ a ∈ A, P a = i) →
        (∀ b ∈ B, P b = i) → #A = t → #B = t → (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) → False := by
  obtain ⟨a, ha⟩ : ∃ a : V → Fin r → ℕ, a = fun w i => #{u ∈ wk26part f i | G.Adj w u} :=
    ⟨_, rfl⟩
  have haT : ∀ w i, a w i ≤ T := by
    intro w i; rw [ha]; exact (card_filter_le _ _).trans (wk26part_card f i).le
  obtain ⟨Fl, hFl⟩ : ∃ Fl : Finset V, Fl = U.filter (fun w => ∀ i, t ≤ a w i) := ⟨_, rfl⟩
  have hFlU : Fl ⊆ U := by rw [hFl]; exact filter_subset _ _
  have hFlc : #Fl < (T.choose t) ^ r * t := by
    refine wk26_filtercount G ht (by omega) f hfree Fl (fun w hw i => ?_)
    rw [hFl, mem_filter] at hw
    have := hw.2 i
    rw [ha] at this
    exact this
  have hex : ∀ w, ∃ i : Fin r, (w ∈ U → w ∉ Fl → a w i < t) := by
    intro w
    by_cases h : w ∈ U ∧ w ∉ Fl
    · have : ¬ ∀ i, t ≤ a w i := fun hall => h.2 (by rw [hFl, mem_filter]; exact ⟨h.1, hall⟩)
      push Not at this
      obtain ⟨i, hi⟩ := this
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨⟨0, by omega⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose ι hι using hex
  obtain ⟨Gd, hGd⟩ : ∃ Gd : Finset V,
      Gd = (U \ Fl).filter (fun w => ∀ i, i ≠ ι w → T ≤ a w i + s) := ⟨_, rfl⟩
  have hGdU : Gd ⊆ U := by rw [hGd]; exact (filter_subset _ _).trans sdiff_subset
  refine ⟨ι, Gd, hGdU, ?_, ?_⟩
  · -- counting the bad vertices
    obtain ⟨miss, hmiss⟩ : ∃ miss : V → ℝ,
        miss = fun w => ∑ i ∈ univ.erase (ι w), ((T : ℝ) - a w i) := ⟨_, rfl⟩
    have hmiss0 : ∀ w, 0 ≤ miss w := by
      intro w; rw [hmiss]
      exact sum_nonneg (fun i _ => by have := haT w i; simp only [sub_nonneg]; exact_mod_cast this)
    have hrr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpv : ∀ w ∈ U \ Fl, (∑ i, (a w i : ℝ)) + miss w ≤ t + ((r : ℝ) - 1) * T := by
      intro w hw
      rw [mem_sdiff] at hw
      have hlt := hι w hw.1 hw.2
      have e1 : (∑ i, (a w i : ℝ)) = a w (ι w) + ∑ i ∈ univ.erase (ι w), (a w i : ℝ) :=
        (Finset.add_sum_erase _ _ (mem_univ _)).symm
      have e2 : miss w = ((r : ℝ) - 1) * T - ∑ i ∈ univ.erase (ι w), (a w i : ℝ) := by
        rw [hmiss]
        simp only [sum_sub_distrib, sum_const, card_erase_of_mem (mem_univ _), card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [Nat.cast_sub hr]
        push_cast
        ring
      have : (a w (ι w) : ℝ) ≤ t := by exact_mod_cast hlt.le
      linarith
    have hFv : ∀ w, (∑ i, (a w i : ℝ)) ≤ r * T := by
      intro w
      calc (∑ i, (a w i : ℝ)) ≤ ∑ _i : Fin r, (T : ℝ) :=
            sum_le_sum (fun i _ => by exact_mod_cast haT w i)
        _ = r * T := by simp
    have hdc : (r : ℝ) * T * ((1 - 1 / (r : ℝ) - α) * #U) ≤ ∑ w ∈ U, ∑ i, (a w i : ℝ) := by
      rw [Finset.sum_comm]
      calc (r : ℝ) * T * ((1 - 1 / (r : ℝ) - α) * #U)
          = ∑ _i : Fin r, (T : ℝ) * ((1 - 1 / (r : ℝ) - α) * #U) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ ∑ i : Fin r, ∑ w ∈ U, (a w i : ℝ) := by
          refine sum_le_sum (fun i _ => ?_)
          have hdci := wk26_dc G (wk26part f i) U
          have : (∑ w ∈ U, (a w i : ℝ)) = ∑ u ∈ wk26part f i, (#{w ∈ U | G.Adj u w} : ℝ) := by
            rw [ha]; exact_mod_cast hdci
          rw [this]
          calc (T : ℝ) * ((1 - 1 / (r : ℝ) - α) * #U)
              = ∑ _u ∈ wk26part f i, ((1 - 1 / (r : ℝ) - α) * #U) := by
                rw [sum_const, wk26part_card, nsmul_eq_mul]
            _ ≤ _ := sum_le_sum (fun u hu => hdeg u (wk26part_sub f U hfU i hu))
    have hsplit : ∑ w ∈ U, ∑ i, (a w i : ℝ) =
        ∑ w ∈ U \ Fl, ∑ i, (a w i : ℝ) + ∑ w ∈ Fl, ∑ i, (a w i : ℝ) :=
      (Finset.sum_sdiff hFlU).symm
    have h1 : ∑ w ∈ U \ Fl, ∑ i, (a w i : ℝ) ≤
        ∑ w ∈ U \ Fl, ((t : ℝ) + ((r : ℝ) - 1) * T - miss w) :=
      sum_le_sum (fun w hw => by linarith [hpv w hw])
    have h2 : ∑ w ∈ Fl, ∑ i, (a w i : ℝ) ≤ #Fl * (r * T) := by
      calc ∑ w ∈ Fl, ∑ i, (a w i : ℝ) ≤ ∑ _w ∈ Fl, ((r : ℝ) * T) := sum_le_sum (fun w _ => hFv w)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    have h3 : ∑ w ∈ U \ Fl, ((t : ℝ) + ((r : ℝ) - 1) * T - miss w) =
        #(U \ Fl) * ((t : ℝ) + ((r : ℝ) - 1) * T) - ∑ w ∈ U \ Fl, miss w := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    have hcardsd : (#(U \ Fl) : ℝ) ≤ #U := by exact_mod_cast card_le_card sdiff_subset
    have hrc : (r : ℝ) * T * ((1 - 1 / (r : ℝ) - α) * #U) =
        ((r : ℝ) - 1) * T * #U - r * T * α * #U := by field_simp
    have hPhi : (#Fl : ℝ) ≤ (T.choose t) ^ r * t := by exact_mod_cast hFlc.le
    have hmisssum : ∑ w ∈ U \ Fl, miss w ≤
        t * #U + (T.choose t) ^ r * t * (r * T) + r * T * α * #U := by
      have hTr : (0 : ℝ) ≤ ((r : ℝ) - 1) * T := by
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr
        positivity
      have : (#(U \ Fl) : ℝ) * ((t : ℝ) + ((r : ℝ) - 1) * T) ≤ #U * ((t : ℝ) + ((r : ℝ) - 1) * T) :=
        mul_le_mul_of_nonneg_right hcardsd (by positivity)
      have : (#Fl : ℝ) * (r * T) ≤ (T.choose t) ^ r * t * (r * T) :=
        mul_le_mul_of_nonneg_right hPhi (by positivity)
      nlinarith
    -- bad vertices have miss >= s + 1
    obtain ⟨Bd, hBd⟩ : ∃ Bd : Finset V,
        Bd = (U \ Fl).filter (fun w => ¬ ∀ i, i ≠ ι w → T ≤ a w i + s) := ⟨_, rfl⟩
    have hBdsub : Bd ⊆ U \ Fl := by rw [hBd]; exact filter_subset _ _
    have hBdm : ∀ w ∈ Bd, (s : ℝ) + 1 ≤ miss w := by
      intro w hw
      rw [hBd, mem_filter] at hw
      have := hw.2
      push Not at this
      obtain ⟨i, hi, hlt⟩ := this
      rw [hmiss]
      have hle : (T : ℝ) - a w i ≤ ∑ j ∈ univ.erase (ι w), ((T : ℝ) - a w j) :=
        Finset.single_le_sum (f := fun j => (T : ℝ) - a w j)
          (fun j _ => by have := haT w j; simp only [sub_nonneg]; exact_mod_cast this)
          (mem_erase.mpr ⟨hi, mem_univ _⟩)
      have : (a w i : ℝ) + s + 1 ≤ T := by exact_mod_cast hlt
      linarith
    have hBdcount : (#Bd : ℝ) * (s + 1) ≤ ∑ w ∈ U \ Fl, miss w := by
      calc (#Bd : ℝ) * (s + 1) = ∑ _w ∈ Bd, ((s : ℝ) + 1) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ w ∈ Bd, miss w := sum_le_sum hBdm
        _ ≤ ∑ w ∈ U \ Fl, miss w :=
          sum_le_sum_of_subset_of_nonneg hBdsub (fun w _ _ => hmiss0 w)
    have hUGd : U \ Gd ⊆ Fl ∪ Bd := by
      intro w hw
      rw [mem_sdiff] at hw
      rw [mem_union]
      by_cases hwF : w ∈ Fl
      · exact Or.inl hwF
      · right
        rw [hBd, mem_filter, mem_sdiff]
        refine ⟨⟨hw.1, hwF⟩, fun hall => hw.2 ?_⟩
        rw [hGd, mem_filter, mem_sdiff]
        exact ⟨⟨hw.1, hwF⟩, hall⟩
    have hcU : (#(U \ Gd) : ℝ) ≤ #Fl + #Bd := by
      have := (card_le_card hUGd).trans (card_union_le _ _)
      exact_mod_cast this
    have hs1 : (0 : ℝ) < s + 1 := by positivity
    have hBd' : (#Bd : ℝ) ≤ (t * #U + (T.choose t) ^ r * t * (r * T) + r * T * α * #U) / (s + 1) := by
      rw [le_div_iff₀ hs1]; linarith
    linarith
  · -- K_{t,t} inside a good class gives K_{r+1}(t)
    intro i A B hA hB hAi hBi hAc hBc hAB
    have hgood : ∀ w ∈ A ∪ B, ∀ j, j ≠ i → T ≤ a w j + s := by
      intro w hw j hj
      have hwGd : w ∈ Gd := by
        rw [mem_union] at hw; rcases hw with h | h; exact hA h; exact hB h
      have hιw : ι w = i := by
        rw [mem_union] at hw; rcases hw with h | h; exact hAi w h; exact hBi w h
      rw [hGd, mem_filter] at hwGd
      exact hwGd.2 j (by rw [hιw]; exact hj)
    obtain ⟨Cm, hCm⟩ : ∃ Cm : Fin r → Finset V,
        Cm = fun j => (wk26part f j).filter (fun u => ∀ w ∈ A ∪ B, G.Adj w u) := ⟨_, rfl⟩
    have hCmcard : ∀ j, j ≠ i → t ≤ #(Cm j) := by
      intro j hj
      have hsub : (wk26part f j).filter (fun u => ¬ ∀ w ∈ A ∪ B, G.Adj w u) ⊆
          (A ∪ B).biUnion (fun w => (wk26part f j).filter (fun u => ¬ G.Adj w u)) := by
        intro u hu
        rw [mem_filter] at hu
        push Not at hu
        obtain ⟨w, hw, hnadj⟩ := hu.2
        rw [mem_biUnion]
        exact ⟨w, hw, mem_filter.mpr ⟨hu.1, hnadj⟩⟩
      have hb1 := (card_le_card hsub).trans card_biUnion_le
      have hb2 : ∑ w ∈ A ∪ B, #((wk26part f j).filter (fun u => ¬ G.Adj w u)) ≤
          ∑ _w ∈ A ∪ B, s := by
        refine sum_le_sum (fun w hw => ?_)
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := wk26part f j) (fun u => G.Adj w u)
        rw [wk26part_card] at hsplit
        have := hgood w hw j hj
        rw [ha] at this
        simp only at this
        omega
      have hAB2 : #(A ∪ B) ≤ 2 * t := by
        have := card_union_le A B; omega
      have hsplit2 := Finset.card_filter_add_card_filter_not
        (s := wk26part f j) (fun u => ∀ w ∈ A ∪ B, G.Adj w u)
      rw [wk26part_card] at hsplit2
      rw [sum_const, smul_eq_mul] at hb2
      have : #(A ∪ B) * s ≤ 2 * t * s := Nat.mul_le_mul_right _ hAB2
      rw [hCm]
      simp only
      omega
    apply hfree
    refine wk26_mkcopy G (r + 1) t (Fin.lastCases B (fun j => if j = i then A else Cm j)) ?_ ?_
    · intro k
      induction k using Fin.lastCases with
      | last => rw [Fin.lastCases_last, hBc]
      | cast j =>
        rw [Fin.lastCases_castSucc]
        split_ifs with hj
        · rw [hAc]
        · exact hCmcard j hj
    · have hCmA : ∀ j, ∀ u ∈ Cm j, ∀ w ∈ A ∪ B, G.Adj w u := by
        intro j u hu
        rw [hCm, mem_filter] at hu
        exact hu.2
      have hCmP : ∀ j, Cm j ⊆ wk26part f j := by
        intro j; rw [hCm]; exact filter_subset _ _
      intro k k' hkk' x hx y hy
      induction k using Fin.lastCases with
      | last =>
        induction k' using Fin.lastCases with
        | last => exact absurd rfl hkk'
        | cast j =>
          rw [Fin.lastCases_last] at hx
          rw [Fin.lastCases_castSucc] at hy
          split_ifs at hy with hj
          · exact (hAB y hy x hx).symm
          · exact hCmA j y hy x (mem_union_right _ hx)
      | cast j =>
        induction k' using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last] at hy
          rw [Fin.lastCases_castSucc] at hx
          split_ifs at hx with hj
          · exact hAB x hx y hy
          · exact (hCmA j x hx y (mem_union_right _ hy)).symm
        | cast j' =>
          rw [Fin.lastCases_castSucc] at hx hy
          have hjj : j ≠ j' := fun h => hkk' (by rw [h])
          split_ifs at hx hy with h1 h2 h2
          · exact absurd (h1.trans h2.symm) hjj
          · exact hCmA j' y hy x (mem_union_left _ hx)
          · exact (hCmA j x hx y (mem_union_left _ hy)).symm
          · exact wk26part_adj f hjj (hCmP j hx) (hCmP j' hy)

-- L2': Erdos-Stone giving a copy inside U
theorem wk26_esmin2 {ε : ℝ} (hε : 0 < ε) (r T : ℕ) : ∃ N : ℕ, ∀ {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V), N ≤ #U →
    (∀ v ∈ U, (1 - 1 / (r : ℝ) + ε) * #U ≤ #{w ∈ U | G.Adj v w}) →
    ∃ f : Copy (completeEquipartiteGraph (r + 1) T) G, ∀ p, f p ∈ U := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_completeEquipartiteGraph_isContained_of_minDegree hε r T)
  refine ⟨N, fun {V} _ _ G _ U hU hdeg => ?_⟩
  let e : Fin #U ≃ U := (U.equivFin).symm
  let G' : SimpleGraph (Fin #U) := G.comap (fun i => ((e i : U) : V))
  have hdeg' : ∀ i, (G'.degree i : ℝ) = #{w ∈ U | G.Adj (e i) w} := by
    intro i
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    norm_cast
    refine Finset.card_bij (fun j _ => (e j : V)) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨(e j).2, hj⟩
    · intro a _ b _ h
      exact e.injective (Subtype.ext h)
    · intro w hw
      simp only [Finset.mem_filter] at hw
      refine ⟨e.symm ⟨w, hw.1⟩, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change G.Adj (e i : V) (e (e.symm ⟨w, hw.1⟩) : V)
      simpa using hw.2
  have hmin : (G'.minDegree : ℝ) ≥ (1 - 1 / (r : ℝ) + ε) * #U := by
    rcases Nat.eq_zero_or_pos #U with h0 | hpos
    · have h0' : ((#U : ℕ) : ℝ) = 0 := by exact_mod_cast h0
      rw [h0', mul_zero]; positivity
    · have : Nonempty (Fin #U) := ⟨⟨0, hpos⟩⟩
      obtain ⟨i, hi⟩ := G'.exists_minimal_degree_vertex
      rw [hi, hdeg' i]
      exact hdeg _ (e i).2
  obtain ⟨g⟩ := hN #U hU hmin
  refine ⟨⟨⟨fun p => (e (g p) : V), fun h => g.toHom.map_adj h⟩, ?_⟩, fun p => (e (g p)).2⟩
  intro p q h
  exact g.injective (e.injective (Subtype.ext h))

-- G restricted to a vertex set W
def wk26res {V : Type*} (G : SimpleGraph V) (W : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ W ∧ b ∈ W
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

theorem wk26res_S {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    [DecidableRel (wk26res G W).Adj] : wk26S (wk26res G W) W = wk26S G W := by
  unfold wk26S
  refine Finset.sum_congr rfl (fun v hv => ?_)
  congr 1
  refine Finset.filter_congr (fun w hw => ?_)
  change G.Adj v w ∧ v ∈ W ∧ w ∈ W ↔ G.Adj v w
  exact ⟨fun h => h.1, fun h => ⟨h, hv, hw⟩⟩

theorem wk26res_free {V : Type*} [DecidableEq V] (G : SimpleGraph V) (W : Finset V) (t : ℕ)
    (ht : 1 ≤ t)
    (h : ∀ A B : Finset V, A ⊆ W → B ⊆ W → #A = t → #B = t →
      (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) → False) :
    ¬ completeEquipartiteGraph (1 + 1) t ⊑ wk26res G W := by
  rintro ⟨g⟩
  have hadj : ∀ j j' : Fin t, (wk26res G W).Adj (g (0, j)) (g (1, j')) := fun j j' =>
    g.toHom.map_adj (show (completeEquipartiteGraph (1 + 1) t).Adj (0, j) (1, j') by
      simp)
  have j0 : Fin t := ⟨0, by omega⟩
  refine h (univ.image (fun j => g (0, j))) (univ.image (fun j => g (1, j))) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_image] at ha
    obtain ⟨j, _, rfl⟩ := ha
    exact (hadj j j0).2.1
  · intro a ha
    rw [mem_image] at ha
    obtain ⟨j, _, rfl⟩ := ha
    exact (hadj j0 j).2.2
  · rw [card_image_of_injective (f := fun j : Fin t => g (0, j)) univ
      (fun j j' hh => (Prod.mk.inj (g.injective hh)).2), card_univ, Fintype.card_fin]
  · rw [card_image_of_injective (f := fun j : Fin t => g (1, j)) univ
      (fun j j' hh => (Prod.mk.inj (g.injective hh)).2), card_univ, Fintype.card_fin]
  · intro a ha b hb
    rw [mem_image] at ha hb
    obtain ⟨j, _, rfl⟩ := ha
    obtain ⟨j', _, rfl⟩ := hb
    exact (hadj j j').1

-- internal pairs of P are covered by the good classes plus the rest
theorem wk26_internal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {r : ℕ} (P : V → Fin r) (Gd : Finset V) :
    ∑ v, #{w | G.Adj v w ∧ P v = P w} ≤
      ∑ i, wk26S G (Gd.filter (fun v => P v = i)) + 2 * Fintype.card V * #(univ \ Gd) := by
  have hv1 : ∀ v ∈ Gd, #{w | G.Adj v w ∧ P v = P w} ≤
      #{w ∈ Gd.filter (fun u => P u = P v) | G.Adj v w} + #(univ \ Gd) := by
    intro v _
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro w hw
    rw [mem_filter] at hw
    rw [mem_union]
    by_cases hwG : w ∈ Gd
    · left
      rw [mem_filter, mem_filter]
      exact ⟨⟨hwG, hw.2.2.symm⟩, hw.2.1⟩
    · right
      exact mem_sdiff.mpr ⟨mem_univ _, hwG⟩
  have hv2 : ∀ v, #{w | G.Adj v w ∧ P v = P w} ≤ Fintype.card V := fun v =>
    (card_filter_le _ _).trans (by rw [card_univ])
  have hsplit := (Finset.sum_sdiff (f := fun v => #{w | G.Adj v w ∧ P v = P w})
    (subset_univ Gd)).symm
  rw [hsplit]
  have hA : ∑ v ∈ Gd, #{w | G.Adj v w ∧ P v = P w} ≤
      ∑ v ∈ Gd, #{w ∈ Gd.filter (fun u => P u = P v) | G.Adj v w} + #Gd * #(univ \ Gd) := by
    calc ∑ v ∈ Gd, #{w | G.Adj v w ∧ P v = P w}
        ≤ ∑ v ∈ Gd, (#{w ∈ Gd.filter (fun u => P u = P v) | G.Adj v w} + #(univ \ Gd)) :=
          sum_le_sum hv1
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have hB : ∑ v ∈ univ \ Gd, #{w | G.Adj v w ∧ P v = P w} ≤ #(univ \ Gd) * Fintype.card V := by
    calc ∑ v ∈ univ \ Gd, #{w | G.Adj v w ∧ P v = P w} ≤ ∑ _v ∈ univ \ Gd, Fintype.card V :=
          sum_le_sum (fun v _ => hv2 v)
      _ = _ := by rw [sum_const, smul_eq_mul]
  have hC : ∑ v ∈ Gd, #{w ∈ Gd.filter (fun u => P u = P v) | G.Adj v w} =
      ∑ i, wk26S G (Gd.filter (fun v => P v = i)) := by
    rw [← Finset.sum_fiberwise Gd P]
    refine sum_congr rfl (fun i _ => ?_)
    unfold wk26S
    refine sum_congr rfl (fun v hv => ?_)
    rw [mem_filter] at hv
    rw [hv.2]
  have hGd : #Gd ≤ Fintype.card V := by rw [← card_univ]; exact card_le_card (subset_univ _)
  have : #Gd * #(univ \ Gd) ≤ Fintype.card V * #(univ \ Gd) := Nat.mul_le_mul_right _ hGd
  rw [hC] at hA
  nlinarith

-- arithmetic for L6
theorem wk26_ar1 (c α β γ n u S : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 16)
    (hβ : β = α * γ / 4) (hu0 : 0 ≤ u) (hlt : u < (1 - γ) * n) (hn : 2 / (α * γ) ≤ n)
    (h1 : (c - α) * u ^ 2 + (α - β) * n ^ 2 - (n - u) ≤ S) (h2 : S ≤ (c + β) * u ^ 2) :
    False := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have k1 : (α - β) * n ^ 2 - n ≤ (α + β) * u ^ 2 := by nlinarith
  have k2 : u ^ 2 < ((1 - γ) * n) ^ 2 := pow_lt_pow_left₀ hlt hu0 (by norm_num)
  have k3 : ((1 - γ) * n) ^ 2 ≤ (1 - γ) * n ^ 2 := by
    have : ((1 - γ) * n) ^ 2 = (1 - γ) * (1 - γ) * n ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have k4 : (α - β) * n ^ 2 - n < (α + β) * ((1 - γ) * n ^ 2) := by
    have := mul_lt_mul_of_pos_left (k2.trans_le k3) (by linarith : 0 < α + β)
    linarith
  have k6 : 1 ≤ α * γ / 2 * n := by
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  have k7 : n ≤ α * γ / 2 * n ^ 2 := by nlinarith
  have e : (α + β) * ((1 - γ) * n ^ 2) = (α - β) * n ^ 2 - (α * γ / 2 + β * γ) * n ^ 2 := by
    rw [hβ]; ring
  have hbg : 0 ≤ β * γ * n ^ 2 := by positivity
  rw [e] at k4
  linarith

theorem wk26_ar2 (c α β n u S NE : ℝ) (hα : 0 < α) (hβα : β ≤ α / 2) (hc : 0 ≤ c - α)
    (hn1 : 1 ≤ n) (hX1 : 2 * (1 + NE ^ 2) / α ≤ n) (hu : u < NE) (hu0 : 0 ≤ u)
    (hS : S ≤ u ^ 2) (h1 : (c - α) * u ^ 2 + (α - β) * n ^ 2 - (n - u) ≤ S) : False := by
  have k1 : S < NE ^ 2 := lt_of_le_of_lt hS (pow_lt_pow_left₀ hu hu0 (by norm_num))
  have k0 : 0 ≤ (c - α) * u ^ 2 := by positivity
  have k2 : α / 2 * n ^ 2 - n ≤ S := by nlinarith
  have k3 : 1 + NE ^ 2 ≤ α / 2 * n := by
    rw [div_le_iff₀ hα] at hX1; linarith
  nlinarith [sq_nonneg NE]

theorem wk26_ar3 (γ n u NS : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 16) (h : (1 - γ) * n ≤ u)
    (hnS : 2 * NS ≤ n) (hNS : 0 ≤ NS) : NS ≤ u := by nlinarith

theorem wk26_ar4 (r' R α : ℝ) (hr' : 1 ≤ r') (hR : R = r' + 1) (hα : 0 < α)
    (hαR : α * R ^ 2 ≤ 1 / 16) : 1 - 1 / r' + 1 / (2 * R ^ 2) ≤ 1 - 1 / R - α := by
  have hR0 : 0 < R := by rw [hR]; linarith
  have e : 1 / r' - 1 / R = 1 / (r' * R) := by
    rw [hR]; field_simp; ring
  have h1 : 1 / R ^ 2 ≤ 1 / (r' * R) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : α ≤ 1 / (2 * R ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : 1 / (2 * R ^ 2) + 1 / (2 * R ^ 2) = 1 / R ^ 2 := by field_simp; ring
  linarith

set_option maxHeartbeats 800000 in
theorem wk26_ar5 (η γ R β₁ Φ T s t n u N1 α I Sw D B : ℝ)
    (hη : 0 < η) (hγ : γ = η / 16) (hRβ : R * β₁ = η / 8) (hR : 0 < R) (hT : 0 < T)
    (hΦ : 0 ≤ Φ) (hs16 : 16 * t ≤ η * (s + 1)) (ht : 0 ≤ t) (hs0 : 0 ≤ s)
    (hαRT : α * R * T ≤ η / 16) (hα : 0 ≤ α) (hn1 : 1 ≤ n)
    (hX3 : 4 / η * (2 * (Φ + Φ * R * T) + R * N1 ^ 2 + 1) ≤ n)
    (hI : I ≤ Sw + 2 * n * D) (hSw : Sw ≤ R * (β₁ * n ^ 2 + N1 ^ 2)) (hD : D ≤ (n - u) + B)
    (hB : B ≤ Φ + (t * n + Φ * (R * T) + R * T * α * n) / (s + 1)) (hu : (1 - γ) * n ≤ u) :
    I ≤ η * n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have hq1 : t * n / (s + 1) ≤ η / 16 * n := by
    rw [div_le_iff₀ hs1]
    nlinarith
  have hq2 : R * T * α * n / (s + 1) ≤ η / 16 * n := by
    rw [div_le_iff₀ hs1]
    have : R * T * α = α * R * T := by ring
    rw [this]
    have k1 : α * R * T * n ≤ η / 16 * n := mul_le_mul_of_nonneg_right hαRT hn0.le
    have k2 : η / 16 * n ≤ η / 16 * n * (s + 1) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  have hq3 : Φ * (R * T) / (s + 1) ≤ Φ * R * T := by
    rw [div_le_iff₀ hs1]
    have : 0 ≤ Φ * R * T := by positivity
    nlinarith
  have hsplitdiv : (t * n + Φ * (R * T) + R * T * α * n) / (s + 1) =
      t * n / (s + 1) + Φ * (R * T) / (s + 1) + R * T * α * n / (s + 1) := by ring
  have hD' : D ≤ γ * n + Φ + η / 16 * n + Φ * R * T + η / 16 * n := by
    have : n - u ≤ γ * n := by linarith
    linarith
  have hR0 : 2 * (Φ + Φ * R * T) + R * N1 ^ 2 + 1 ≤ η / 4 * n := by
    have e : 4 / η * (2 * (Φ + Φ * R * T) + R * N1 ^ 2 + 1) =
        (2 * (Φ + Φ * R * T) + R * N1 ^ 2 + 1) / (η / 4) := by field_simp
    rw [e, div_le_iff₀ (by positivity)] at hX3
    linarith
  have hcnt : 2 * n * D ≤ 2 * n * (γ * n + Φ + η / 16 * n + Φ * R * T + η / 16 * n) :=
    mul_le_mul_of_nonneg_left hD' (by positivity)
  have e : R * (β₁ * n ^ 2 + N1 ^ 2) +
      2 * n * (γ * n + Φ + η / 16 * n + Φ * R * T + η / 16 * n) =
      (R * β₁) * n ^ 2 + R * N1 ^ 2 + 2 * γ * n ^ 2 +
        η / 4 * n ^ 2 + 2 * (Φ + Φ * R * T) * n := by ring
  have hN0 : 0 ≤ R * N1 ^ 2 := by positivity
  have hP0 : 0 ≤ 2 * (Φ + Φ * R * T) := by positivity
  have h1 : R * N1 ^ 2 ≤ η / 4 * n ^ 2 := by
    have k : R * N1 ^ 2 ≤ η / 4 * n := by linarith
    have k2 : η / 4 * n ≤ η / 4 * n * n := le_mul_of_one_le_right (by positivity) hn1
    have : η / 4 * n * n = η / 4 * n ^ 2 := by ring
    linarith
  have h2 : 2 * (Φ + Φ * R * T) * n ≤ η / 4 * n ^ 2 := by
    have k : 2 * (Φ + Φ * R * T) ≤ η / 4 * n := by linarith
    have k2 := mul_le_mul_of_nonneg_right k hn0.le
    have : η / 4 * n * n = η / 4 * n ^ 2 := by ring
    linarith
  have hfin : R * (β₁ * n ^ 2 + N1 ^ 2) +
      2 * n * (γ * n + Φ + η / 16 * n + Φ * R * T + η / 16 * n) ≤ η * n ^ 2 := by
    rw [e, hRβ, hγ]
    linarith
  linarith

-- L6: Erdos-Simonovits edge stability for K_{r+1}(t)-free graphs
set_option maxHeartbeats 2000000 in
theorem wk26_stab {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ β : ℝ, 0 < β ∧ ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], ¬ completeEquipartiteGraph (r + 1) t ⊑ G → N ≤ Fintype.card V →
    (1 - 1 / (r : ℝ) - β) * (Fintype.card V : ℝ) ^ 2 ≤ wk26S G univ →
    ∃ P : V → Fin r,
      (∑ v, (#{w | G.Adj v w ∧ P v = P w} : ℝ)) ≤ η * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hr' : 1 ≤ r' := by omega
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ((r' + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hR2 : (2 : ℝ) ≤ R := by rw [hRdef]; exact_mod_cast (by omega : 2 ≤ r' + 1)
  have hRr' : R = (r' : ℝ) + 1 := by rw [hRdef]; push_cast; ring
  have hr'1 : (1 : ℝ) ≤ r' := by exact_mod_cast hr'
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = ⌈16 * t / η⌉₊ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 2 * t * s + t := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by omega
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hT1r : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hs16 : 16 * (t : ℝ) ≤ η * (s + 1) := by
    have h1 := Nat.le_ceil (16 * (t : ℝ) / η)
    rw [← hs] at h1
    rw [div_le_iff₀ hη] at h1
    have : (0 : ℝ) ≤ η := hη.le
    linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = η / 16 := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = η / (16 * R ^ 2 * T) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = α * γ / 4 := ⟨_, rfl⟩
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : ℝ, β₁ = η / (8 * R) := ⟨_, rfl⟩
  have hαpos : 0 < α := by rw [hα]; positivity
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ1 : γ ≤ 1 / 16 := by rw [hγ]; linarith
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hβα : β ≤ α / 2 := by
    rw [hβ]
    have : α * γ ≤ α * (1 / 16) := mul_le_mul_of_nonneg_left hγ1 hαpos.le
    linarith
  have hβ₁pos : 0 < β₁ := by rw [hβ₁]; positivity
  have hαR : α * R ^ 2 ≤ 1 / 16 := by
    rw [hα]
    have : η / (16 * R ^ 2 * T) * R ^ 2 = η / (16 * T) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hαRT : α * R * T ≤ η / 16 := by
    rw [hα]
    have : η / (16 * R ^ 2 * T) * R * T = η / (16 * R) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : η * 1 ≤ η * R := mul_le_mul_of_nonneg_left (by linarith) hη.le
    linarith
  obtain ⟨NS, hNS⟩ := wk26_esmin2 (ε := 1 / (2 * R ^ 2)) (by positivity) r' T
  obtain ⟨NE, hNE⟩ := wk26_ese (r := r' + 1) (t := t) (by omega) hβpos
  obtain ⟨N1, hN1⟩ := wk26_ese (r := 1) (t := t) le_rfl hβ₁pos
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = (((T.choose t) ^ (r' + 1) * t : ℕ) : ℝ) := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ Φ := by rw [hΦ]; positivity
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 2 * (1 + (NE : ℝ) ^ 2) / α + 2 / (α * γ) +
      4 / η * (2 * (Φ + Φ * R * T) + R * (N1 : ℝ) ^ 2 + 1) := ⟨_, rfl⟩
  refine ⟨β, hβpos, ⌈X⌉₊ + 2 * NS + 1, ?_⟩
  intro V _ _ G _ hfree hN hS
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card V := ⟨_, rfl⟩
  rw [← hn] at hN hS ⊢
  rw [← hRdef] at hS
  have hnX : X ≤ n := by
    have h1 := Nat.le_ceil X
    have : ⌈X⌉₊ ≤ n := by omega
    have : (⌈X⌉₊ : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnS : (2 * NS : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * NS ≤ n)
  have hA1 : 0 ≤ 2 * (1 + (NE : ℝ) ^ 2) / α := by positivity
  have hA2 : 0 ≤ 2 / (α * γ) := by positivity
  have hA3 : 0 ≤ 4 / η * (2 * (Φ + Φ * R * T) + R * (N1 : ℝ) ^ 2 + 1) := by positivity
  have hX1 : 2 * (1 + (NE : ℝ) ^ 2) / α ≤ n := by linarith
  have hX2 : 2 / (α * γ) ≤ n := by linarith
  have hX3 : 4 / η * (2 * (Φ + Φ * R * T) + R * (N1 : ℝ) ^ 2 + 1) ≤ n := by linarith
  have hinvR : 0 < 1 / R := by positivity
  have hc0 : 0 ≤ 1 - 1 / R - α := by
    have : 1 / R ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have : α * 4 ≤ α * R ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hαpos.le
    linarith
  -- step 2: deletion
  have hcard : #(univ : Finset V) = n := by rw [card_univ, hn]
  obtain ⟨U, -, hSU, hdegU⟩ := wk26_del G (1 - 1 / R - α) ((α - β) * (n : ℝ) ^ 2)
    (by linarith) univ n univ hcard (subset_refl _) (by
      rw [hcard, sub_self, sub_zero]
      have : (1 - 1 / R - α) * (n : ℝ) ^ 2 + (α - β) * (n : ℝ) ^ 2 =
          (1 - 1 / R - β) * (n : ℝ) ^ 2 := by ring
      linarith)
  rw [hcard] at hSU
  have hUn : (#U : ℝ) ≤ n := by
    have := card_le_card (subset_univ U)
    rw [hcard] at this
    exact_mod_cast this
  have hU0 : (0 : ℝ) ≤ #U := by positivity
  have hSUle : (wk26S G U : ℝ) ≤ (#U : ℝ) ^ 2 := by
    have := wk26S_le G U
    rw [sq]; exact_mod_cast this
  -- step 3: U is almost everything
  have hUbig : (1 - γ) * n ≤ #U := by
    by_contra hlt
    push Not at hlt
    by_cases hUE : NE ≤ #U
    · have hup := hNE G hfree U hUE
      rw [← hRdef] at hup
      exact wk26_ar1 (1 - 1 / R) α β γ n #U (wk26S G U) hαpos hγpos hγ1 hβ hU0 hlt hX2
        (by linarith) (by linarith)
    · push Not at hUE
      have : (#U : ℝ) < NE := by exact_mod_cast hUE
      exact wk26_ar2 (1 - 1 / R) α β n #U (wk26S G U) NE hαpos hβα (by linarith) hn1 hX1 this
        hU0 hSUle (by linarith)
  -- step 4: a K_r(T) inside U
  have hUS : NS ≤ #U := by
    have : (NS : ℝ) ≤ #U := wk26_ar3 γ n #U NS hγpos.le hγ1 hUbig hnS (by positivity)
    exact_mod_cast this
  have hcoef := wk26_ar4 r' R α hr'1 hRr' hαpos hαR
  obtain ⟨f, hfU⟩ := hNS G U hUS (fun v hv => by
    have := hdegU v hv
    have : (1 - 1 / (r' : ℝ) + 1 / (2 * R ^ 2)) * #U ≤ (1 - 1 / R - α) * #U :=
      mul_le_mul_of_nonneg_right hcoef hU0
    linarith)
  -- step 5: classification
  obtain ⟨P, Gd, hGdU, hbad, hKtt⟩ := wk26_core G (r := r' + 1) (t := t) (T := T) (s := s)
    (by omega) ht (by omega) hfree U α (by rw [← hRdef]; exact hdegU) f hfU
  refine ⟨P, ?_⟩
  -- step 6: the good classes are sparse
  have hWi : ∀ i : Fin (r' + 1), (wk26S G (Gd.filter (fun v => P v = i)) : ℝ) ≤
      β₁ * (n : ℝ) ^ 2 + (N1 : ℝ) ^ 2 := by
    intro i
    have hWn : (#(Gd.filter (fun v => P v = i)) : ℝ) ≤ n := by
      have := card_le_card (subset_univ (Gd.filter (fun v => P v = i)))
      rw [hcard] at this
      exact_mod_cast this
    have hSW : (wk26S G (Gd.filter (fun v => P v = i)) : ℝ) ≤
        (#(Gd.filter (fun v => P v = i)) : ℝ) ^ 2 := by
      have := wk26S_le G (Gd.filter (fun v => P v = i))
      rw [sq]; exact_mod_cast this
    have hN10 : (0 : ℝ) ≤ (N1 : ℝ) ^ 2 := by positivity
    have hβn : (0 : ℝ) ≤ β₁ * (n : ℝ) ^ 2 := by positivity
    by_cases hWN : N1 ≤ #(Gd.filter (fun v => P v = i))
    · have hfreeW := wk26res_free G (Gd.filter (fun v => P v = i)) t ht
        (fun A B hA hB hAc hBc hAB =>
          hKtt i A B (hA.trans (filter_subset _ _)) (hB.trans (filter_subset _ _))
            (fun a ha => (mem_filter.mp (hA ha)).2) (fun b hb => (mem_filter.mp (hB hb)).2)
            hAc hBc hAB)
      have h1 := hN1 (wk26res G (Gd.filter (fun v => P v = i))) hfreeW _ hWN
      rw [wk26res_S] at h1
      have e1 : (1 - 1 / ((1 : ℕ) : ℝ) + β₁) = β₁ := by simp
      rw [e1] at h1
      have hnn : (#(Gd.filter (fun v => P v = i)) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hWn 2
      have : β₁ * (#(Gd.filter (fun v => P v = i)) : ℝ) ^ 2 ≤ β₁ * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hnn hβ₁pos.le
      linarith
    · push Not at hWN
      have h1 : (#(Gd.filter (fun v => P v = i)) : ℝ) ≤ N1 := by exact_mod_cast hWN.le
      have : (#(Gd.filter (fun v => P v = i)) : ℝ) ^ 2 ≤ (N1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      linarith
  -- step 7: count
  have hint := wk26_internal G P Gd
  rw [← hn] at hint
  have hint' : (∑ v, (#{w | G.Adj v w ∧ P v = P w} : ℝ)) ≤
      ∑ i, (wk26S G (Gd.filter (fun v => P v = i)) : ℝ) + 2 * n * #(univ \ Gd) := by
    exact_mod_cast hint
  have hsumW : ∑ i : Fin (r' + 1), (wk26S G (Gd.filter (fun v => P v = i)) : ℝ) ≤
      R * (β₁ * (n : ℝ) ^ 2 + (N1 : ℝ) ^ 2) := by
    calc ∑ i : Fin (r' + 1), (wk26S G (Gd.filter (fun v => P v = i)) : ℝ)
        ≤ ∑ _i : Fin (r' + 1), (β₁ * (n : ℝ) ^ 2 + (N1 : ℝ) ^ 2) := sum_le_sum (fun i _ => hWi i)
      _ = R * (β₁ * (n : ℝ) ^ 2 + (N1 : ℝ) ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hRdef]
  have hcomp : (#(univ \ Gd) : ℝ) ≤ (n - #U) + #(U \ Gd) := by
    have hsub : univ \ Gd ⊆ (univ \ U) ∪ (U \ Gd) := by
      intro w hw
      rw [mem_union, mem_sdiff, mem_sdiff]
      rw [mem_sdiff] at hw
      by_cases hwU : w ∈ U
      · exact Or.inr ⟨hwU, hw.2⟩
      · exact Or.inl ⟨mem_univ _, hwU⟩
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 : #(univ \ U) = n - #U := by
      rw [card_sdiff_of_subset (subset_univ U), hcard]
    rw [h2] at h1
    have h3 : (((n - #U : ℕ)) : ℝ) = n - #U := by
      rw [Nat.cast_sub]
      have := card_le_card (subset_univ U); rw [hcard] at this; exact this
    have : (#(univ \ Gd) : ℝ) ≤ ((n - #U : ℕ) : ℝ) + #(U \ Gd) := by exact_mod_cast h1
    linarith
  rw [← hRdef] at hbad
  have hbad' : (#(U \ Gd) : ℝ) ≤ Φ + (t * n + Φ * (R * T) + R * T * α * n) / (s + 1) := by
    have hs1 : (0 : ℝ) < s + 1 := by positivity
    have : (t * #U + Φ * (R * T) + R * T * α * #U) / (s + 1) ≤
        (t * n + Φ * (R * T) + R * T * α * n) / (s + 1) := by
      apply div_le_div_of_nonneg_right _ hs1.le
      have : (t : ℝ) * #U ≤ t * n := mul_le_mul_of_nonneg_left hUn (by positivity)
      have : R * T * α * #U ≤ R * T * α * n := mul_le_mul_of_nonneg_left hUn (by positivity)
      linarith
    have hΦ' : ((T.choose t : ℕ) : ℝ) ^ (r' + 1) * t = Φ := by rw [hΦ]; push_cast; ring
    rw [hΦ'] at hbad
    linarith
  -- step 8: arithmetic
  have hRβ : R * β₁ = η / 8 := by rw [hβ₁]; field_simp
  exact wk26_ar5 η γ R β₁ Φ T s t n #U N1 α _ _ _ _ hη hγ hRβ (by linarith) hTpos hΦ0 hs16
    (by positivity) (by positivity) hαRT hαpos.le hn1 hX3 hint' hsumW hcomp hbad' hUbig

-- rebalancing permutation (copied from the lemma_3_9 sibling, wkx39_sigma)
theorem wk26_sigma {n r : ℕ} (hr : 0 < r) (P : Fin n → Fin r) (B : Finset (Fin n)) (m : ℕ)
    (hB : ∀ i : Fin r, (B.filter (fun b => P b = i)).card ≤ m) (hn : r * m ≤ n) :
    ∃ σ : Fin n ≃ Fin n, ∀ b ∈ B, (σ b : ℕ) % r = P b := by
  classical
  let k : Fin n → ℕ := fun b => ((B.filter (fun c => P c = P b)).filter (fun c => c < b)).card
  have hk : ∀ b ∈ B, k b < m := by
    intro b hb
    have : k b < (B.filter (fun c => P c = P b)).card :=
      Finset.card_lt_card (Finset.filter_ssubset.2 ⟨b, by simp [hb], lt_irrefl b⟩)
    exact lt_of_lt_of_le this (hB _)
  have hlt : ∀ b ∈ B, (P b : ℕ) + r * k b < n := by
    intro b hb
    have h1 := hk b hb
    have h2 := (P b).isLt
    have : r * (k b + 1) ≤ r * m := Nat.mul_le_mul_left _ h1
    nlinarith
  let f : Fin n → Fin n := fun b => if h : (P b : ℕ) + r * k b < n then ⟨_, h⟩ else b
  have hf : ∀ b ∈ B, (f b : ℕ) = P b + r * k b := fun b hb => by
    simp only [f, dif_pos (hlt b hb)]
  have hmod : ∀ b ∈ B, (f b : ℕ) % r = P b := by
    intro b hb
    rw [hf b hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (P b).isLt]
  have hsub : ∀ b c, b ∈ B → c ∈ B → P b = P c → b < c → k b < k c := by
    intro b c hb hc hPbc hbc
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨b, by simp [hb, hPbc, hbc], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨⟨hx.1.1, hx.1.2.trans hPbc⟩, hx.2.trans hbc⟩
  have hinj : Set.InjOn f B := by
    intro b hb c hc hbc
    have hb' : b ∈ B := hb
    have hc' : c ∈ B := hc
    have h := congrArg (fun x : Fin n => (x : ℕ)) hbc
    have hPbc : P b = P c := by
      apply Fin.ext
      rw [← hmod b hb', ← hmod c hc']
      exact congrArg (· % r) h
    rw [hf b hb', hf c hc', hPbc] at h
    have hkk : k b = k c := Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel h)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt' | hlt'
    · have := hsub b c hb' hc' hPbc hlt'
      omega
    · have := hsub c b hc' hb' hPbc.symm hlt'
      omega
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := (Finset.univ : Finset (Fin n))) (by simp) (Finset.subset_univ _) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun b hb => ?_⟩
  have : ((g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ)) b : Fin n) = f b := hg b hb
  rw [this]
  exact hmod b hb


-- generic covering: pairs inside B governed by q, the rest touch univ \ B
theorem wk26_cover {V : Type*} [Fintype V] [DecidableEq V] (p q : V → V → Prop)
    [∀ v w, Decidable (p v w)] [∀ v w, Decidable (q v w)] (B : Finset V)
    (h : ∀ v ∈ B, ∀ w ∈ B, p v w → q v w) :
    ∑ v, #{w | p v w} ≤ ∑ v, #{w | q v w} + 2 * Fintype.card V * #(univ \ B) := by
  have hv1 : ∀ v ∈ B, #{w | p v w} ≤ #{w | q v w} + #(univ \ B) := by
    intro v hv
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro w hw
    rw [mem_filter] at hw
    rw [mem_union]
    by_cases hwB : w ∈ B
    · left
      rw [mem_filter]
      exact ⟨mem_univ _, h v hv w hwB hw.2⟩
    · right
      exact mem_sdiff.mpr ⟨mem_univ _, hwB⟩
  have hv2 : ∀ v, #{w | p v w} ≤ Fintype.card V := fun v =>
    (card_filter_le _ _).trans (by rw [card_univ])
  have hsplit := (Finset.sum_sdiff (f := fun v => #{w | p v w}) (subset_univ B)).symm
  rw [hsplit]
  have hA : ∑ v ∈ B, #{w | p v w} ≤ ∑ v ∈ B, #{w | q v w} + #B * #(univ \ B) := by
    calc ∑ v ∈ B, #{w | p v w} ≤ ∑ v ∈ B, (#{w | q v w} + #(univ \ B)) := sum_le_sum hv1
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have hB' : ∑ v ∈ univ \ B, #{w | p v w} ≤ #(univ \ B) * Fintype.card V := by
    calc ∑ v ∈ univ \ B, #{w | p v w} ≤ ∑ _v ∈ univ \ B, Fintype.card V :=
          sum_le_sum (fun v _ => hv2 v)
      _ = _ := by rw [sum_const, smul_eq_mul]
  have hq : ∑ v ∈ B, #{w | q v w} ≤ ∑ v, #{w | q v w} :=
    sum_le_sum_of_subset (subset_univ _)
  have hBc : #B ≤ Fintype.card V := by rw [← card_univ]; exact card_le_card (subset_univ _)
  have : #B * #(univ \ B) ≤ Fintype.card V * #(univ \ B) := Nat.mul_le_mul_right _ hBc
  nlinarith

-- balancing a partition into a labelling of the Turan graph
theorem wk26_balance {n r : ℕ} (hr : 0 < r) (P : Fin n → Fin r) :
    ∃ σ : Fin n ≃ Fin n, ∃ B : Finset (Fin n), (∀ b ∈ B, (σ b : ℕ) % r = P b) ∧
      ((#(univ \ B) : ℕ) : ℝ) ^ 2 ≤
        2 * r * ∑ i, ((#{v | P v = i} : ℕ) : ℝ) ^ 2 - 2 * (n : ℝ) ^ 2 + 2 * (r : ℝ) ^ 2 := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, m = n / r := ⟨_, rfl⟩
  have hex : ∀ i : Fin r, ∃ Bi ⊆ (univ : Finset (Fin n)).filter (fun v => P v = i),
      #Bi = min (#{v | P v = i}) m := fun i => Finset.exists_subset_card_eq (min_le_left _ _)
  choose Bf hBf1 hBf2 using hex
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin n), B = univ.biUnion Bf := ⟨_, rfl⟩
  have hBfil : ∀ i, B.filter (fun b => P b = i) = Bf i := by
    intro i
    ext b
    rw [hB, mem_filter, mem_biUnion]
    constructor
    · rintro ⟨⟨j, _, hj⟩, hPb⟩
      have := (mem_filter.mp (hBf1 j hj)).2
      rw [hPb] at this
      subst this
      exact hj
    · intro hb
      exact ⟨⟨i, mem_univ _, hb⟩, (mem_filter.mp (hBf1 i hb)).2⟩
  obtain ⟨σ, hσ⟩ := wk26_sigma hr P B m
    (fun i => by rw [hBfil, hBf2]; exact min_le_right _ _) (by rw [hm]; exact Nat.mul_div_le n r)
  refine ⟨σ, B, hσ, ?_⟩
  have hBcard : #B = ∑ i, min (#{v | P v = i}) m := by
    rw [card_eq_sum_card_fiberwise (f := P) (t := univ) (fun _ _ => mem_univ _)]
    refine sum_congr rfl (fun i _ => ?_)
    rw [hBfil, hBf2]
  have hncnt : n = ∑ i, #{v | P v = i} := by
    have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (f := P) (t := univ)
      (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_fin] at this
    exact this
  have hD : #(univ \ B) = n - #B := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have hBn : #B ≤ n := by
    have := card_le_card (subset_univ B); rwa [card_univ, Fintype.card_fin] at this
  -- real-valued bookkeeping
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨c, hc⟩ : ∃ c : Fin r → ℝ, c = fun i => ((#{v | P v = i} : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin r → ℝ, x = fun i => c i - ((min (#{v | P v = i}) m : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hDx : ((#(univ \ B) : ℕ) : ℝ) = ∑ i, x i := by
    rw [hD, Nat.cast_sub hBn, hBcard, hx, hc]
    push_cast
    rw [sum_sub_distrib]
    congr 1
    conv_lhs => rw [hncnt]
    push_cast
    rfl
  have hmr : (n : ℝ) / r < m + 1 := by
    have h1 := Nat.div_add_mod n r
    have h2 := Nat.mod_lt n hr
    rw [div_lt_iff₀ hrpos]
    have : (n : ℝ) = r * m + (n % r : ℕ) := by rw [hm]; exact_mod_cast h1.symm
    have h3 : ((n % r : ℕ) : ℝ) < r := by exact_mod_cast h2
    nlinarith
  have hxle : ∀ i, 0 ≤ x i ∧ x i ≤ |c i - n / r| + 1 := by
    intro i
    rw [hx, hc]
    simp only
    rcases le_total (#{v | P v = i}) m with h | h
    · rw [min_eq_left h, sub_self]
      exact ⟨le_rfl, by positivity⟩
    · rw [min_eq_right h]
      have : (m : ℝ) ≤ ((#{v | P v = i} : ℕ) : ℝ) := by exact_mod_cast h
      refine ⟨by linarith, ?_⟩
      have := le_abs_self (((#{v | P v = i} : ℕ) : ℝ) - n / r)
      linarith
  have hx2 : ∀ i, x i ^ 2 ≤ 2 * (c i - n / r) ^ 2 + 2 := by
    intro i
    obtain ⟨h0, h1⟩ := hxle i
    have : x i ^ 2 ≤ (|c i - n / r| + 1) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have e : (|c i - n / r| + 1) ^ 2 = |c i - n / r| ^ 2 + 2 * |c i - n / r| + 1 := by ring
    rw [e, sq_abs] at this
    nlinarith [sq_nonneg (|c i - n / r| - 1), sq_abs (c i - n / r)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin r)) (fun _ => (1 : ℝ)) x
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hsumc : ∑ i, c i = n := by
    have := congrArg (Nat.cast : ℕ → ℝ) hncnt
    push_cast at this
    rw [hc]
    exact this.symm
  have hvar : ∑ i, (c i - n / r) ^ 2 = ∑ i, c i ^ 2 - (n : ℝ) ^ 2 / r := by
    have e : ∀ i, (c i - n / r) ^ 2 = c i ^ 2 - 2 * (n / r) * c i + (n / r) ^ 2 := fun i => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsumc]
    field_simp
    ring
  have hsx : ∑ i, x i ^ 2 ≤ 2 * (∑ i, c i ^ 2 - (n : ℝ) ^ 2 / r) + 2 * r := by
    calc ∑ i, x i ^ 2 ≤ ∑ i, (2 * (c i - n / r) ^ 2 + 2) := sum_le_sum (fun i _ => hx2 i)
      _ = 2 * (∑ i, c i ^ 2 - (n : ℝ) ^ 2 / r) + 2 * r := by
        rw [sum_add_distrib, ← mul_sum, hvar]; simp; ring
  rw [hDx]
  have hc2 : ∑ i, ((#{v | P v = i} : ℕ) : ℝ) ^ 2 = ∑ i, c i ^ 2 := by rw [hc]
  rw [hc2]
  have : (r : ℝ) * (2 * (∑ i, c i ^ 2 - (n : ℝ) ^ 2 / r) + 2 * r) =
      2 * r * ∑ i, c i ^ 2 - 2 * (n : ℝ) ^ 2 + 2 * (r : ℝ) ^ 2 := by
    field_simp
  calc (∑ i, x i) ^ 2 ≤ r * ∑ i, x i ^ 2 := hcs
    _ ≤ r * (2 * (∑ i, c i ^ 2 - (n : ℝ) ^ 2 / r) + 2 * r) :=
      mul_le_mul_of_nonneg_left hsx hrpos.le
    _ = _ := this

-- L7: few internal pairs + many edges => close to a labelled Turan graph
set_option maxHeartbeats 1000000 in
theorem wk26_fin {n r : ℕ} (hr : 1 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Fin n → Fin r) (η β : ℝ)
    (hint : (∑ v, (#{w | G.Adj v w ∧ P v = P w} : ℝ)) ≤ η * (n : ℝ) ^ 2)
    (hS : (1 - 1 / (r : ℝ) - β) * (n : ℝ) ^ 2 ≤ wk26S G univ) :
    ∃ σ : Fin n ≃ Fin n, ∃ D : ℝ, 0 ≤ D ∧
      D ^ 2 ≤ 2 * r * (β + η) * (n : ℝ) ^ 2 + 2 * (r : ℝ) ^ 2 ∧
      (∑ v, (#{w | G.Adj v w ∧ (σ v : ℕ) % r = (σ w : ℕ) % r} : ℝ)) +
      (∑ v, (#{w | (σ v : ℕ) % r ≠ (σ w : ℕ) % r ∧ ¬ G.Adj v w} : ℝ)) ≤
        (β + 2 * η) * (n : ℝ) ^ 2 + 4 * n * D := by
  classical
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨ir, hir⟩ : ∃ ir : ℝ, ir = 1 / r := ⟨_, rfl⟩
  have hrir : (r : ℝ) * ir = 1 := by rw [hir]; field_simp
  rw [← hir] at hS
  obtain ⟨σ, B, hσ, hDsq⟩ := wk26_balance (by omega) P
  have hsplitA : ∀ v, (#{w | G.Adj v w} : ℝ) =
      #{w | G.Adj v w ∧ P v = P w} + #{w | G.Adj v w ∧ ¬ P v = P w} := by
    intro v
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n)).filter (G.Adj v)) (fun w => P v = P w)
    rw [Finset.filter_filter, Finset.filter_filter] at this
    exact_mod_cast this.symm
  have hsplitB : ∀ v, (#{w | ¬ P v = P w} : ℝ) =
      #{w | G.Adj v w ∧ ¬ P v = P w} + #{w | ¬ P v = P w ∧ ¬ G.Adj v w} := by
    intro v
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n)).filter (fun w => ¬ P v = P w)) (G.Adj v)
    rw [Finset.filter_filter, Finset.filter_filter] at this
    have e : #{w | ¬ P v = P w ∧ G.Adj v w} = #{w | G.Adj v w ∧ ¬ P v = P w} := by
      congr 1
      ext w
      simp only [mem_filter, mem_univ, true_and]
      exact and_comm
    rw [e] at this
    exact_mod_cast this.symm
  have hsplitC : ∀ v, (#{w | ¬ P v = P w} : ℝ) = n - #{w | P w = P v} := by
    intro v
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun w => P v = P w)
    rw [card_univ, Fintype.card_fin] at this
    have e : #{w | P v = P w} = #{w | P w = P v} := by
      congr 1
      ext w
      simp only [mem_filter, mem_univ, true_and]
      exact eq_comm
    rw [e] at this
    have h' : (#{w | P w = P v} : ℝ) + #{w | ¬ P v = P w} = n := by exact_mod_cast this
    linarith
  have hQ2 : ∑ v, (#{w | P w = P v} : ℝ) = ∑ i, ((#{v | P v = i} : ℕ) : ℝ) ^ 2 := by
    rw [← Finset.sum_fiberwise univ P (fun v => (#{w | P w = P v} : ℝ))]
    refine sum_congr rfl (fun i _ => ?_)
    have : ∀ v ∈ (univ : Finset (Fin n)).filter (fun v => P v = i),
        (#{w | P w = P v} : ℝ) = ((#{v | P v = i} : ℕ) : ℝ) := by
      intro v hv
      rw [mem_filter] at hv
      rw [hv.2]
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul, sq]
  have hSsum : (wk26S G univ : ℝ) = ∑ v, (#{w | G.Adj v w} : ℝ) := by
    unfold wk26S
    push_cast
    rfl
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin r)) (fun _ => (1 : ℝ))
    (fun i => ((#{v | P v = i} : ℕ) : ℝ))
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hCS
  have hncnt : ∑ i, ((#{v | P v = i} : ℕ) : ℝ) = n := by
    have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (f := P) (t := univ)
      (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_fin] at this
    have := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    exact this.symm
  rw [hncnt] at hCS
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∑ v, (#{w | G.Adj v w ∧ P v = P w} : ℝ) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ v, (#{w | G.Adj v w ∧ ¬ P v = P w} : ℝ) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ v, (#{w | ¬ P v = P w ∧ ¬ G.Adj v w} : ℝ) := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2d⟩ : ∃ Q2 : ℝ, Q2 = ∑ i, ((#{v | P v = i} : ℕ) : ℝ) ^ 2 := ⟨_, rfl⟩
  have hSIC : (wk26S G univ : ℝ) = I + C := by
    rw [hSsum, hI, hC, ← sum_add_distrib]
    exact sum_congr rfl (fun v _ => hsplitA v)
  have hCM : C + M = (n : ℝ) * n - Q2 := by
    rw [hC, hM, ← sum_add_distrib, hQ2d, ← hQ2]
    rw [show (n : ℝ) * n = ∑ _v : Fin n, (n : ℝ) by simp, ← sum_sub_distrib]
    refine sum_congr rfl (fun v _ => ?_)
    rw [← hsplitB v, hsplitC v]
  rw [← hQ2d] at hCS hDsq
  rw [← hI] at hint
  have hQ2low : (n : ℝ) ^ 2 * 1 ≤ r * Q2 := by linarith
  have hMb : M ≤ (β + η) * (n : ℝ) ^ 2 := by
    have k1 : (r : ℝ) * ir * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 := by rw [hrir, one_mul]
    have k2 : ir * ((n : ℝ) ^ 2 * 1) ≤ ir * (r * Q2) :=
      mul_le_mul_of_nonneg_left hQ2low (by rw [hir]; positivity)
    have k3 : ir * (r * Q2) = Q2 := by rw [← mul_assoc, mul_comm ir, hrir, one_mul]
    linarith
  have hQ2up : (r : ℝ) * Q2 ≤ (n : ℝ) ^ 2 + r * (β + η) * (n : ℝ) ^ 2 := by
    have k1 : Q2 ≤ (ir + β + η) * (n : ℝ) ^ 2 := by
      have : 0 ≤ M := by rw [hM]; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      linarith
    have k2 := mul_le_mul_of_nonneg_left k1 hrpos.le
    have k3 : (r : ℝ) * ((ir + β + η) * (n : ℝ) ^ 2) =
        (r * ir) * (n : ℝ) ^ 2 + r * (β + η) * (n : ℝ) ^ 2 := by ring
    rw [k3, hrir, one_mul] at k2
    exact k2
  refine ⟨σ, ((#(univ \ B) : ℕ) : ℝ), by positivity, by linarith, ?_⟩
  · have hc1 := wk26_cover (fun v w => G.Adj v w ∧ (σ v : ℕ) % r = (σ w : ℕ) % r)
      (fun v w => G.Adj v w ∧ P v = P w) B (by
        intro v hv w hw h
        refine ⟨h.1, Fin.ext ?_⟩
        rw [← hσ v hv, ← hσ w hw]
        exact h.2)
    have hc2 := wk26_cover (fun v w => (σ v : ℕ) % r ≠ (σ w : ℕ) % r ∧ ¬ G.Adj v w)
      (fun v w => ¬ P v = P w ∧ ¬ G.Adj v w) B (by
        intro v hv w hw h
        refine ⟨fun hPe => h.1 ?_, h.2⟩
        rw [hσ v hv, hσ w hw, hPe])
    rw [Fintype.card_fin] at hc1 hc2
    have hc1' : (∑ v, (#{w | G.Adj v w ∧ (σ v : ℕ) % r = (σ w : ℕ) % r} : ℝ)) ≤
        I + 2 * n * ((#(univ \ B) : ℕ) : ℝ) := by
      rw [hI]; exact_mod_cast hc1
    have hc2' : (∑ v, (#{w | (σ v : ℕ) % r ≠ (σ w : ℕ) % r ∧ ¬ G.Adj v w} : ℝ)) ≤
        M + 2 * n * ((#(univ \ B) : ℕ) : ℝ) := by
      rw [hM]; exact_mod_cast hc2
    linarith

theorem wk26_edgecount {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype H.edgeSet] [DecidableRel G.Adj] [DecidableRel H.Adj] :
    2 * #(G.edgeFinset \ H.edgeFinset) = ∑ v, #{w | G.Adj v w ∧ ¬ H.Adj v w} := by
  classical
  have e : G.edgeFinset \ H.edgeFinset = (G \ H).edgeFinset := by
    ext e
    simp only [mem_sdiff, mem_edgeFinset, edgeSet_sdiff, Set.mem_diff]
  rw [e]
  have h1 : ∑ v, (G \ H).degree v = 2 * #(G \ H).edgeFinset := by
    convert sum_degrees_eq_twice_card_edges (G \ H)
  have h2 : ∀ v, (G \ H).degree v = #{w | G.Adj v w ∧ ¬ H.Adj v w} := by
    intro v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    congr 1
  rw [← Finset.sum_congr rfl (fun v _ => h2 v)]
  convert h1.symm

theorem wk26_final {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype H.edgeSet] [DecidableRel G.Adj] [DecidableRel H.Adj] (X : ℝ)
    (h : (∑ v, (#{w | G.Adj v w ∧ ¬ H.Adj v w} : ℝ)) +
      (∑ v, (#{w | H.Adj v w ∧ ¬ G.Adj v w} : ℝ)) ≤ 2 * X) :
    ((G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card : ℝ) ≤ X := by
  have e1 := wk26_edgecount G H
  have e2 := wk26_edgecount H G
  have e1' : 2 * ((G.edgeFinset \ H.edgeFinset).card : ℝ) =
      ∑ v, (#{w | G.Adj v w ∧ ¬ H.Adj v w} : ℝ) := by exact_mod_cast e1
  have e2' : 2 * ((H.edgeFinset \ G.edgeFinset).card : ℝ) =
      ∑ v, (#{w | H.Adj v w ∧ ¬ G.Adj v w} : ℝ) := by exact_mod_cast e2
  linarith

-- spectral helpers (copied from the lemma_2_3 sibling solution Sol_pv_9a5da411)
open Matrix in
theorem wk26_transpose {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hA

open Matrix in
theorem wk26_exists {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) :
    ∃ v : n → ℝ, v ⬝ᵥ v = 1 ∧ A *ᵥ v = hA.eigenvalues₀ ⟨0, h⟩ • v := by
  obtain ⟨j, hj⟩ : ∃ j : n, j = (Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨0, h⟩ :=
    ⟨_, rfl⟩
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis j), ?_, ?_⟩
  · have horth := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal j j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at horth
    simpa using horth
  · rw [hA.mulVec_eigenvectorBasis]
    congr 1
    rw [hj]
    simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

open Matrix in
theorem wk26_row {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (i : V) :
    (G.adjMatrix ℝ *ᵥ x) i = ∑ j, (if G.Adj i j then x j else 0) := by
  simp only [mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

-- main theorem
open Classical WangKangXue.SpectralTuran in
theorem solution {W : Type*} [Fintype W] (F : SimpleGraph W) (r : ℕ) (hr : 2 ≤ r)
    (hχ : F.chromaticNumber = ((r + 1 : ℕ) : ℕ∞)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      F.Free G → (1 - 1 / (r : ℝ) - δ) * n ≤ specRad G →
      ∃ H : SimpleGraph (Fin n), Nonempty (H ≃g SimpleGraph.turanGraph n r) ∧
        ((G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card : ℝ) ≤
          ε * (n : ℝ) ^ 2 := by
  intro ε hε
  have hcol : F.Colorable (r + 1) := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable, hχ]
  obtain ⟨t, ht⟩ : ∃ t, t = Fintype.card W + 1 := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by omega
  have hfreeK : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), F.Free G →
      ¬ completeEquipartiteGraph (r + 1) t ⊑ G := by
    intro n G hF hK
    obtain ⟨C⟩ := hcol
    apply hF
    refine (isContained_completeEquipartiteGraph_of_colorable C t (fun c => ?_)).trans hK
    exact le_trans (Fintype.card_le_of_injective _ Subtype.val_injective)
      (by omega : Fintype.card W ≤ t)
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε']; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε']; exact min_le_left _ _
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (ε' / 4) (ε' ^ 2 / (128 * r)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min (by positivity) (by positivity)
  have hηa : η ≤ ε' / 4 := by rw [hη]; exact min_le_left _ _
  have hηb : η ≤ ε' ^ 2 / (128 * r) := by rw [hη]; exact min_le_right _ _
  have hη1 : η ≤ 1 := by linarith
  obtain ⟨β₀, hβ₀, Nst, hNst⟩ := wk26_stab (r := r) (t := t) hr ht1 hη0 hη1
  obtain ⟨βs, hβs⟩ : ∃ βs : ℝ, βs = min β₀ (ε' ^ 2 / (128 * r)) := ⟨_, rfl⟩
  have hβs0 : 0 < βs := by rw [hβs]; exact lt_min hβ₀ (by positivity)
  have hβsa : βs ≤ β₀ := by rw [hβs]; exact min_le_left _ _
  have hβsb : βs ≤ ε' ^ 2 / (128 * r) := by rw [hβs]; exact min_le_right _ _
  have hsmall : ε' ^ 2 / (128 * r) ≤ ε' / 256 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ε' ^ 2 ≤ ε' := by nlinarith
    nlinarith
  obtain ⟨Nsp, hNsp⟩ := wk26_spec (r := r) (t := t) (by omega) (β := βs / 2) (by positivity)
  refine ⟨βs / 4, by positivity, Nst + Nsp + ⌈8 * r / ε'⌉₊ + 1, ?_⟩
  intro n hn G hF hlam
  have hK := hfreeK G hF
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcard : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn0
  -- eigenvector
  obtain ⟨x, hxx, hAx⟩ := wk26_exists (G.isHermitian_adjMatrix ℝ) hcard
  have hspec : specRad G = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hcard⟩ := by
    unfold specRad
    rw [dif_pos hcard]
  rw [← hspec] at hAx
  obtain ⟨lam, hlamd⟩ : ∃ lam, lam = specRad G := ⟨_, rfl⟩
  rw [← hlamd] at hAx hlam
  have heig : ∀ u, lam * x u = ∑ v ∈ univ.filter (G.Adj u), x v := by
    intro u
    have := congrFun hAx u
    rw [wk26_row, Pi.smul_apply, smul_eq_mul] at this
    rw [← this, Finset.sum_filter]
  have hx2 : ∑ u, x u ^ 2 = 1 := by
    rw [← hxx]
    simp only [dotProduct, sq]
  have hinvr : 1 / (r : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]; linarith
  have hβs1 : βs ≤ 1 / 256 := by
    have : ε' / 256 ≤ 1 / 256 := by linarith
    linarith
  have hc4 : 1 / 4 ≤ 1 - 1 / (r : ℝ) - βs / 4 := by linarith
  have hlam4 : (Fintype.card (Fin n) : ℝ) / 4 ≤ lam := by
    rw [Fintype.card_fin]
    have := mul_le_mul_of_nonneg_right hc4 hnr.le
    linarith
  have hsp := hNsp G hK (by rw [Fintype.card_fin]; omega) x lam hx2 hlam4 heig
  -- edges from the spectral radius
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 - 1 / (r : ℝ) := ⟨_, rfl⟩
  rw [← hc] at hsp
  have hS : (1 - 1 / (r : ℝ) - βs) * (n : ℝ) ^ 2 ≤ wk26S G univ := by
    rw [← hc]
    have hl0 : 0 ≤ (c - βs / 4) * n := by
      have : 1 / 4 ≤ c - βs / 4 := by rw [hc]; exact hc4
      positivity
    have h1 : ((c - βs / 4) * n) ^ 2 ≤ lam ^ 2 :=
      pow_le_pow_left₀ hl0 (by rw [hc]; exact hlam) 2
    have e : (c + βs / 2) * ((c - βs) * (n : ℝ) ^ 2) =
        ((c - βs / 4) * n) ^ 2 - 9 * βs ^ 2 / 16 * (n : ℝ) ^ 2 := by ring
    have h9 : 0 ≤ 9 * βs ^ 2 / 16 * (n : ℝ) ^ 2 := by positivity
    have key : (c + βs / 2) * ((c - βs) * (n : ℝ) ^ 2) ≤ (c + βs / 2) * wk26S G univ := by
      linarith
    have hpos : 0 < c + βs / 2 := by
      have : 1 / 4 ≤ c - βs / 4 := by rw [hc]; exact hc4
      linarith
    exact le_of_mul_le_mul_left key hpos
  -- stability
  have hS0 : (1 - 1 / (r : ℝ) - β₀) * (Fintype.card (Fin n) : ℝ) ^ 2 ≤ wk26S G univ := by
    rw [Fintype.card_fin]
    have : (1 - 1 / (r : ℝ) - β₀) * (n : ℝ) ^ 2 ≤ (1 - 1 / (r : ℝ) - βs) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  obtain ⟨P, hP⟩ := hNst G hK (by rw [Fintype.card_fin]; omega) hS0
  rw [Fintype.card_fin] at hP
  obtain ⟨σ, D, hD0, hD2, hsum⟩ := wk26_fin (by omega) G P η βs hP hS
  -- the error term D
  have hn8 : 8 * (r : ℝ) / ε' ≤ n := by
    have h1 := Nat.le_ceil (8 * (r : ℝ) / ε')
    have : (⌈8 * (r : ℝ) / ε'⌉₊ : ℝ) ≤ n := by
      have : ⌈8 * (r : ℝ) / ε'⌉₊ ≤ n := by omega
      exact_mod_cast this
    linarith
  have hDle : D ≤ ε' * n / 4 := by
    have h8 : 8 * (r : ℝ) ≤ ε' * n := by
      rw [div_le_iff₀ hε'0] at hn8; linarith
    have hr2' : 2 * (r : ℝ) ^ 2 ≤ ε' ^ 2 / 32 * (n : ℝ) ^ 2 := by
      have : (8 * (r : ℝ)) ^ 2 ≤ (ε' * n) ^ 2 := pow_le_pow_left₀ (by positivity) h8 2
      linarith
    have hb : 2 * r * (βs + η) * (n : ℝ) ^ 2 ≤ ε' ^ 2 / 32 * (n : ℝ) ^ 2 := by
      have h1 : 2 * (r : ℝ) * (βs + η) ≤ ε' ^ 2 / 32 := by
        have e : (r : ℝ) * (ε' ^ 2 / (128 * r)) = ε' ^ 2 / 128 := by field_simp
        have hs2 : βs + η ≤ 2 * (ε' ^ 2 / (128 * r)) := by linarith
        have := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ 2 * r)
        have e2 : 2 * (r : ℝ) * (2 * (ε' ^ 2 / (128 * r))) = 4 * ((r : ℝ) * (ε' ^ 2 / (128 * r))) := by
          ring
        rw [e2, e] at this
        linarith
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    by_contra hlt
    push Not at hlt
    have : (ε' * n / 4) * (ε' * n / 4) < D * D := mul_self_lt_mul_self (by positivity) hlt
    linarith
  -- the labelled Turan graph
  obtain ⟨H, hHdef⟩ : ∃ H : SimpleGraph (Fin n),
      H = SimpleGraph.comap (fun v : Fin n => (σ v : ℕ) % r) ⊤ := ⟨_, rfl⟩
  have hHadj : ∀ v w, H.Adj v w ↔ (σ v : ℕ) % r ≠ (σ w : ℕ) % r := by
    intro v w
    rw [hHdef]
    simp
  refine ⟨H, ⟨{ toEquiv := σ, map_rel_iff' := ?_ }⟩, ?_⟩
  · intro a b
    rw [SimpleGraph.turanGraph_adj, hHadj]
  · refine wk26_final G H _ ?_
    have f1 : ∑ v, (#{w | G.Adj v w ∧ ¬ H.Adj v w} : ℝ) =
        ∑ v, (#{w | G.Adj v w ∧ (σ v : ℕ) % r = (σ w : ℕ) % r} : ℝ) := by
      refine sum_congr rfl (fun v _ => ?_)
      congr 2 <;> ext w <;> simp [hHadj]
    have f2 : ∑ v, (#{w | H.Adj v w ∧ ¬ G.Adj v w} : ℝ) =
        ∑ v, (#{w | (σ v : ℕ) % r ≠ (σ w : ℕ) % r ∧ ¬ G.Adj v w} : ℝ) := by
      refine sum_congr rfl (fun v _ => ?_)
      congr 2 <;> ext w <;> simp [hHadj]
    rw [f1, f2]
    have h4 : 4 * (n : ℝ) * D ≤ ε' * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hDle (by positivity : (0 : ℝ) ≤ 4 * n)
      linarith
    have hb2 : (βs + 2 * η) * (n : ℝ) ^ 2 ≤ (3 * ε' / 4) * (n : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith
    have hεn : ε' * (n : ℝ) ^ 2 ≤ ε * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hε'ε (sq_nonneg _)
    have hn2 : 0 ≤ ε' * (n : ℝ) ^ 2 := by positivity
    linarith
