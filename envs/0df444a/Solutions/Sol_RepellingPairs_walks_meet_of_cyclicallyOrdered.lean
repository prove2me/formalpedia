-- Prove2me | solution 1 for RepellingPairs.walks_meet_of_cyclicallyOrdered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:51:24.984198+00:00
-- url     : https://prove2.me/submissions/44085b9a-b2af-4009-bef7-6ee8529e09e7

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_DiskEmbedding
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_CyclicallyOrdered
universe u v

section
set_option autoImplicit false


namespace RepellingPairs.Dev.Cross

open Complex

theorem one_sub_div_mem_slitPlane {z W : ℂ} (hz : ‖z‖ ≤ 1) (hW : ‖W‖ = 1) (hne : z ≠ W) :
    1 - z / W ∈ slitPlane := by
  have hW0 : W ≠ 0 := by rintro rfl; simp at hW
  rw [mem_slitPlane_iff]
  have hre : (z / W).re ≤ 1 := by
    calc (z / W).re ≤ ‖z / W‖ := re_le_norm _
      _ = ‖z‖ := by rw [norm_div, hW, div_one]
      _ ≤ 1 := hz
  by_cases h : (z / W).re < 1
  · left; simp only [sub_re, one_re]; linarith
  · right
    intro him
    apply hne
    have h1 : (z / W).re = 1 := le_antisymm hre (not_lt.mp h)
    have h2 : z / W = 1 := by
      apply Complex.ext
      · simpa using h1
      · simp only [sub_im, one_im] at him; simp only [one_im]; linarith
    rwa [div_eq_one_iff_eq hW0] at h2

theorem edge_lift {L w : unitInterval → ℂ} {c : ℂ} (hL : Continuous L) (hw : Continuous w)
    (hslit : ∀ x, w x ∈ slitPlane) (hexp : ∀ x, exp (L x) = c * w x) :
    L 1 - L 0 = log (w 1) - log (w 0) := by
  have hw0 : ∀ x, w x ≠ 0 := fun x => slitPlane_ne_zero (hslit x)
  set M : unitInterval → ℂ := fun x => L 0 - log (w 0) + log (w x) with hM
  have hMc : Continuous M := continuous_const.add (hw.clog hslit)
  have hexpM : ∀ x, exp (M x) = c * w x := by
    intro x
    simp only [hM, exp_add, exp_sub, exp_log (hw0 0), exp_log (hw0 x), hexp 0]
    field_simp [hw0 0]
  have key : L = M := isCoveringMap_exp.eq_of_comp_eq hL hMc
    (by funext x; simp only [Function.comp, hexp, hexpM]) 0 (by simp [hM])
  have := congrFun key 1
  rw [this]; simp only [hM]; ring

theorem arg_one_sub_exp_pos {φ : ℝ} (h0 : 0 < φ) (h1 : φ < 2 * Real.pi) :
    arg (1 - exp (φ * I)) = (φ - Real.pi) / 2 := by
  have hs : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc2 : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at this
    nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
  have hs2 : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have := Real.sin_two_mul (φ / 2)
    rwa [show 2 * (φ / 2) = φ by ring] at this
  have heq : 1 - exp (φ * I) = ((2 * Real.sin (φ / 2) : ℝ) : ℂ) *
      (Real.cos ((φ - Real.pi) / 2) + Real.sin ((φ - Real.pi) / 2) * I) := by
    have e1 : (φ - Real.pi) / 2 = φ / 2 - Real.pi / 2 := by ring
    rw [e1, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    apply Complex.ext
    · simp only [sub_re, one_re, exp_ofReal_mul_I_re, mul_re, ofReal_re, ofReal_im, add_re,
        add_im, mul_im, I_re, I_im]
      rw [hc2]; ring
    · simp only [sub_im, one_im, exp_ofReal_mul_I_im, mul_re, mul_im, ofReal_re, ofReal_im,
        add_re, add_im, I_re, I_im]
      rw [hs2]; ring
  rw [heq, arg_real_mul _ (by linarith)]
  rw [ofReal_cos, ofReal_sin, arg_cos_add_sin_mul_I]
  constructor <;> linarith [Real.pi_pos]

theorem arg_one_sub_exp_neg {φ : ℝ} (h0 : φ < 0) (h1 : -(2 * Real.pi) < φ) :
    arg (1 - exp (φ * I)) = (φ + Real.pi) / 2 := by
  have : exp (φ * I) = exp (((φ + 2 * Real.pi : ℝ) : ℂ) * I) := by
    rw [show (((φ + 2 * Real.pi : ℝ) : ℂ) * I) = φ * I + 2 * Real.pi * I by push_cast; ring,
      exp_add, exp_two_pi_mul_I, mul_one]
  rw [this, arg_one_sub_exp_pos (by linarith) (by linarith)]
  ring

theorem exp_div_exp (x y : ℝ) : exp (x * I) / exp (y * I) = exp (((x - y : ℝ) : ℂ) * I) := by
  rw [← exp_sub]; congr 1; push_cast; ring

/-- Two curves in the closed unit disk joining alternating boundary points meet. -/
theorem paths_meet {A B C D : ℂ} (α : Path A C) (β : Path B D)
    (hα : ∀ s, ‖α s‖ ≤ 1) (hβ : ∀ t, ‖β t‖ ≤ 1)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d - a < 2 * Real.pi)
    (hA : A = exp (a * I)) (hB : B = exp (b * I)) (hC : C = exp (c * I))
    (hD : D = exp (d * I)) :
    ∃ s t, α s = β t := by
  by_contra hcon
  push Not at hcon
  have hAn : ‖A‖ = 1 := hA ▸ norm_exp_ofReal_mul_I a
  have hBn : ‖B‖ = 1 := hB ▸ norm_exp_ofReal_mul_I b
  have hCn : ‖C‖ = 1 := hC ▸ norm_exp_ofReal_mul_I c
  have hDn : ‖D‖ = 1 := hD ▸ norm_exp_ofReal_mul_I d
  have hA0 : A ≠ 0 := by rintro rfl; simp at hAn
  have hB0 : B ≠ 0 := by rintro rfl; simp at hBn
  have hC0 : C ≠ 0 := by rintro rfl; simp at hCn
  have hD0 : D ≠ 0 := by rintro rfl; simp at hDn
  let H : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun st => ⟨α st.1 - β st.2, sub_ne_zero.mpr (hcon _ _)⟩,
      ((α.continuous.comp continuous_fst).sub (β.continuous.comp continuous_snd)).subtype_mk _⟩
  have slA : ∀ t, 1 - β t / A ∈ slitPlane := fun t =>
    one_sub_div_mem_slitPlane (hβ t) hAn (fun h => hcon 0 t (by rw [α.source, h]))
  let f : C(unitInterval, ℂ) := ⟨fun t => log A + log (1 - β t / A),
    continuous_const.add ((continuous_const.sub (β.continuous.div_const A)).clog slA)⟩
  have H_0 : ∀ t, H (0, t) = (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) (f t) := by
    intro t
    apply Subtype.ext
    simp only [H, f, ContinuousMap.coe_mk, exp_add, exp_log hA0,
      exp_log (slitPlane_ne_zero (slA t)), α.source]
    field_simp
  let L := isCoveringMap_exp.liftHomotopy H f H_0
  have hL : ∀ s t, exp (L (s, t)) = α s - β t := by
    intro s t
    have := congrFun (isCoveringMap_exp.liftHomotopy_lifts H f H_0) (s, t)
    exact congrArg Subtype.val this
  have hLc : Continuous L := L.continuous
  -- edge 1: t = 0
  have e1 := edge_lift (L := fun x => L (x, 0)) (w := fun x => 1 - α x / B) (c := -B)
    (hLc.comp (Continuous.prodMk_left 0)) (continuous_const.sub (α.continuous.div_const B))
    (fun x => one_sub_div_mem_slitPlane (hα x) hBn (fun h => hcon x 0 (by rw [β.source, h])))
    (fun x => by rw [hL, β.source]; field_simp; ring)
  -- edge 2: s = 1
  have e2 := edge_lift (L := fun x => L (1, x)) (w := fun x => 1 - β x / C) (c := C)
    (hLc.comp (Continuous.prodMk_right 1)) (continuous_const.sub (β.continuous.div_const C))
    (fun x => one_sub_div_mem_slitPlane (hβ x) hCn (fun h => hcon 1 x (by rw [α.target, h])))
    (fun x => by rw [hL, α.target]; field_simp)
  -- edge 3: t = 1
  have e3 := edge_lift (L := fun x => L (x, 1)) (w := fun x => 1 - α x / D) (c := -D)
    (hLc.comp (Continuous.prodMk_left 1)) (continuous_const.sub (α.continuous.div_const D))
    (fun x => one_sub_div_mem_slitPlane (hα x) hDn (fun h => hcon x 1 (by rw [β.target, h])))
    (fun x => by rw [hL, β.target]; field_simp; ring)
  -- edge 4: s = 0
  have e4 := edge_lift (L := fun x => L (0, x)) (w := fun x => 1 - β x / A) (c := A)
    (hLc.comp (Continuous.prodMk_right 0)) (continuous_const.sub (β.continuous.div_const A))
    slA
    (fun x => by rw [hL, α.source]; field_simp)
  simp only [α.source, α.target, β.source, β.target] at e1 e2 e3 e4
  have hsum : (log (1 - C / B) - log (1 - A / B)) + (log (1 - D / C) - log (1 - B / C))
      - (log (1 - C / D) - log (1 - A / D)) - (log (1 - D / A) - log (1 - B / A)) = 0 := by
    rw [← e1, ← e2, ← e3, ← e4]; ring
  have him := congrArg Complex.im hsum
  simp only [sub_im, add_im, log_im, zero_im] at him
  rw [hA, hB, hC, hD] at him
  simp only [exp_div_exp] at him
  have h1 := arg_one_sub_exp_pos (φ := c - b) (by linarith) (by linarith)
  have h2 := arg_one_sub_exp_neg (φ := a - b) (by linarith) (by linarith)
  have h3 := arg_one_sub_exp_pos (φ := d - c) (by linarith) (by linarith)
  have h4 := arg_one_sub_exp_neg (φ := b - c) (by linarith) (by linarith)
  have h5 := arg_one_sub_exp_neg (φ := c - d) (by linarith) (by linarith)
  have h6 := arg_one_sub_exp_neg (φ := a - d) (by linarith) (by linarith)
  have h7 := arg_one_sub_exp_pos (φ := d - a) (by linarith) (by linarith)
  have h8 := arg_one_sub_exp_pos (φ := b - a) (by linarith) (by linarith)
  linarith [Real.pi_pos]

section walks

variable {V : Type u} {E : Type v} {G : Multigraph V E} (emb : DiskEmbedding G)

/-- `z` lies on the curve drawn by the walk `p`: at a vertex of `p`, or on the arc of an edge of `p`
both of whose ends are vertices of `p`. -/
def OnWalk {x y : V} (p : G.Walk x y) (z : ℂ) : Prop :=
  (∃ v ∈ p.support, z = emb.pos v) ∨
    (∃ e ∈ p.edges, (∀ w, w ∈ G.ends e → w ∈ p.support) ∧
      ∃ s ∈ Set.Icc (0 : ℝ) 1, z = emb.arc e s)

theorem start_mem_support {x y : V} (p : G.Walk x y) : x ∈ p.support := by
  cases p <;> simp [Multigraph.Walk.support]

theorem exists_edge_path (e : E) {x y : V} (h : G.ends e = s(x, y)) :
    ∃ γ : Path (emb.pos x) (emb.pos y), ∀ t, ∃ s ∈ Set.Icc (0 : ℝ) 1, γ t = emb.arc e s := by
  obtain ⟨u, w, hends, h0, h1⟩ := emb.arc_ends e
  have hc : Continuous (fun t : unitInterval => emb.arc e t) :=
    (emb.arc_continuousOn e).comp_continuous continuous_subtype_val (fun t => t.2)
  let γ : Path (emb.pos u) (emb.pos w) :=
    ⟨⟨fun t => emb.arc e t, hc⟩, by simpa using h0, by simpa using h1⟩
  have hγ : ∀ t, ∃ s ∈ Set.Icc (0 : ℝ) 1, γ t = emb.arc e s := fun t => ⟨t, t.2, rfl⟩
  rw [h] at hends
  rcases Sym2.eq_iff.mp hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨γ, hγ⟩
  · exact ⟨γ.symm, fun t => hγ _⟩

theorem exists_walk_path {x y : V} (p : G.Walk x y) :
    ∃ γ : Path (emb.pos x) (emb.pos y), ∀ t, OnWalk emb p (γ t) := by
  induction p with
  | nil v =>
    exact ⟨Path.refl _, fun t => Or.inl ⟨v, by simp [Multigraph.Walk.support], rfl⟩⟩
  | @cons x' y' w' e h p ih =>
    obtain ⟨γ, hγ⟩ := ih
    obtain ⟨δ, hδ⟩ := exists_edge_path emb e h
    refine ⟨δ.trans γ, fun t => ?_⟩
    have hmem : (δ.trans γ) t ∈ Set.range δ ∪ Set.range γ := by
      rw [← Path.trans_range]; exact ⟨t, rfl⟩
    rcases hmem with ⟨t', ht'⟩ | ⟨t', ht'⟩
    · obtain ⟨s, hs, hz⟩ := hδ t'
      right
      refine ⟨e, by simp [Multigraph.Walk.edges], ?_, s, hs, by rw [← ht', hz]⟩
      intro w hw
      rw [h] at hw
      simp only [Multigraph.Walk.support, List.mem_cons]
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (start_mem_support p)
    · rcases hγ t' with ⟨v, hv, hz⟩ | ⟨f, hf, hends, s, hs, hz⟩
      · left
        exact ⟨v, by simp [Multigraph.Walk.support, hv], by rw [← ht', hz]⟩
      · right
        exact ⟨f, by simp [Multigraph.Walk.edges, hf],
          fun w hw => by simp [Multigraph.Walk.support, hends w hw], s, hs, by rw [← ht', hz]⟩

variable {emb}

theorem OnWalk.normalize {x y : V} {p : G.Walk x y} {z : ℂ} (hz : OnWalk emb p z) :
    (∃ v ∈ p.support, z = emb.pos v) ∨
    (∃ e ∈ p.edges, (∀ w, w ∈ G.ends e → w ∈ p.support) ∧
      ∃ s ∈ Set.Ioo (0 : ℝ) 1, z = emb.arc e s) := by
  rcases hz with h | ⟨e, he, hends, s, hs, rfl⟩
  · exact Or.inl h
  · obtain ⟨u, w, hue, h0, h1⟩ := emb.arc_ends e
    rcases eq_or_lt_of_le hs.1 with h | h
    · left
      subst h
      exact ⟨u, hends u (by rw [hue]; exact Sym2.mem_mk_left _ _), h0⟩
    rcases eq_or_lt_of_le hs.2 with h' | h'
    · left
      subst h'
      exact ⟨w, hends w (by rw [hue]; exact Sym2.mem_mk_right _ _), h1⟩
    · right
      exact ⟨e, he, hends, s, ⟨h, h'⟩, rfl⟩

theorem meet_of_onWalk {a b c d : V} {p : G.Walk a b} {q : G.Walk c d} {z : ℂ}
    (hp : OnWalk emb p z) (hq : OnWalk emb q z) : ∃ v, v ∈ p.support ∧ v ∈ q.support := by
  rcases hp.normalize with ⟨v, hv, rfl⟩ | ⟨e, he, hends, s, hs, rfl⟩ <;>
    rcases hq.normalize with ⟨v', hv', hz⟩ | ⟨f, hf, hends', r, hr, hz⟩
  · exact ⟨v, hv, (emb.pos_injective hz) ▸ hv'⟩
  · exact absurd hz.symm (emb.arc_interior_avoids_pos f r hr v)
  · exact absurd hz (emb.arc_interior_avoids_pos e s hs v')
  · by_cases hef : e = f
    · subst hef
      obtain ⟨u, w, hue, -, -⟩ := emb.arc_ends e
      have hm : u ∈ G.ends e := by rw [hue]; exact Sym2.mem_mk_left _ _
      exact ⟨u, hends u hm, hends' u hm⟩
    · have := emb.arc_disjoint e f hef s (Set.Ioo_subset_Icc_self hs) r
        (Set.Ioo_subset_Icc_self hr) hz
      rcases this.1 with h | h <;> linarith [hs.1, hs.2]

theorem OnWalk.norm_le {x y : V} {p : G.Walk x y} {z : ℂ} (hz : OnWalk emb p z) : ‖z‖ ≤ 1 := by
  rcases hz with ⟨v, -, rfl⟩ | ⟨e, -, -, s, hs, rfl⟩
  exacts [emb.pos_mem_disk v, emb.arc_mem_disk e s hs]

theorem meet_of_paths {a b c d : V} {p : G.Walk a b} {q : G.Walk c d} {X Y Z W : ℂ}
    (α : Path X Y) (β : Path Z W) (hα : ∀ t, OnWalk emb p (α t)) (hβ : ∀ t, OnWalk emb q (β t))
    (h : ∃ s t, α s = β t) : ∃ v, v ∈ p.support ∧ v ∈ q.support := by
  obtain ⟨s, t, hst⟩ := h
  exact meet_of_onWalk (hα s) (hst ▸ hβ t)

theorem onWalk_symm {a b : V} {p : G.Walk a b} {X Y : ℂ} (α : Path X Y)
    (hα : ∀ t, OnWalk emb p (α t)) : ∀ t, OnWalk emb p (α.symm t) := fun t => by
  rw [Path.symm_apply]; exact hα _

end walks

theorem core_meet {V : Type u} {E : Type v} {k : ℕ} (G : OSInstance V E k) {i j l m : Fin k}
    (h1 : i < j) (h2 : j < l) (h3 : l < m)
    (α : Path (G.emb.pos (G.term i)) (G.emb.pos (G.term l)))
    (β : Path (G.emb.pos (G.term j)) (G.emb.pos (G.term m)))
    (hα : ∀ s, ‖α s‖ ≤ 1) (hβ : ∀ t, ‖β t‖ ≤ 1) : ∃ s t, α s = β t :=
  paths_meet α β hα hβ (G.θ_strictMono h1) (G.θ_strictMono h2) (G.θ_strictMono h3)
    (by linarith [G.θ_lt_two_pi m, G.θ_nonneg i]) (G.pos_term i) (G.pos_term j) (G.pos_term l)
    (G.pos_term m)

end RepellingPairs.Dev.Cross

namespace RepellingPairs

open RepellingPairs.Dev.Cross

theorem chk_walks_meet_of_cyclicallyOrdered {V : Type u} {E : Type v} {k : ℕ}
    (G : OSInstance V E k) {a b c d : Fin k} (h : CyclicallyOrdered a b c d)
    (p : G.graph.Walk (G.term a) (G.term c)) (q : G.graph.Walk (G.term b) (G.term d)) :
    ∃ v, v ∈ p.support ∧ v ∈ q.support := by
  obtain ⟨γp, hp⟩ := exists_walk_path G.emb p
  obtain ⟨γq, hq⟩ := exists_walk_path G.emb q
  have np : ∀ t, ‖γp t‖ ≤ 1 := fun t => (hp t).norm_le
  have nq : ∀ t, ‖γq t‖ ≤ 1 := fun t => (hq t).norm_le
  have nps : ∀ t, ‖γp.symm t‖ ≤ 1 := fun t => (onWalk_symm γp hp t).norm_le
  have nqs : ∀ t, ‖γq.symm t‖ ≤ 1 := fun t => (onWalk_symm γq hq t).norm_le
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact meet_of_paths γp γq hp hq (core_meet G h1 h2 h3 γp γq np nq)
  · obtain ⟨v, hv1, hv2⟩ := meet_of_paths γq γp.symm hq (onWalk_symm γp hp)
      (core_meet G h1 h2 h3 γq γp.symm nq nps)
    exact ⟨v, hv2, hv1⟩
  · exact meet_of_paths γp.symm γq.symm (onWalk_symm γp hp) (onWalk_symm γq hq)
      (core_meet G h1 h2 h3 γp.symm γq.symm nps nqs)
  · obtain ⟨v, hv1, hv2⟩ := meet_of_paths γq.symm γp (onWalk_symm γq hq) hp
      (core_meet G h1 h2 h3 γq.symm γp nqs np)
    exact ⟨v, hv2, hv1⟩

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_walks_meet_of_cyclicallyOrdered := @RepellingPairs.chk_walks_meet_of_cyclicallyOrdered
