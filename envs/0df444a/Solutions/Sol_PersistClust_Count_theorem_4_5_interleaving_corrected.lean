-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_interleaving_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T15:42:56.256971+00:00
-- url     : https://prove2.me/submissions/e491c25b-c766-4465-8629-79a2478ceec4

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_FiltrationLaw

open Bundle
open scoped ContDiff Manifold

open PersistClust.Count
open scoped ENNReal

/-! ### Helper lemmas -/

/-- Symmetry of reachability along a symmetric relation. -/
theorem t45geo_rtgen_symm {ι : Type*} {R : ι → ι → Prop}
    (hsym : ∀ a b, R a b → R b a) {i j : ι}
    (h : Relation.ReflTransGen R i j) : Relation.ReflTransGen R j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.head (hsym _ _ hbc)

/-- The Rips step relation on level `t` is symmetric (the Rips graph is undirected). -/
theorem t45geo_RipsRel_symm {ι : Type*} (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ t : ℝ) :
    ∀ a b, (fun a b => t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) a b →
      (fun a b => t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) b a :=
  fun _ _ ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩

/-- The superlevel-set filtration with its path-component relation is a genuine filtration:
this is exactly `FiltrationLaw` assembled from the basic `JoinedIn` lemmas. -/
theorem t45geo_super_filtrationLaw {X : Type*} [TopologicalSpace X] (f : X → ℝ) :
    FiltrationLaw (superlevel f) (fun t => JoinedIn (superlevel f t)) where
  antitone := by
    intro s t hst x hx
    exact hst.trans hx
  mem := by
    intro t x y h
    exact JoinedIn.mem h
  refl := by
    intro t x hx
    exact JoinedIn.refl hx
  symm := by
    intro t x y h
    exact JoinedIn.symm h
  trans := by
    intro t x y z h1 h2
    exact JoinedIn.trans h1 h2
  compat := by
    intro s t hst x y h
    exact JoinedIn.mono h (fun z hz => hst.trans hz)

/-- The Rips join relation `ripsJoined` (reachability in the undirected Rips graph on the induced
subgraph `L^t`) is a genuine filtration: the relation is a symmetric, transitive, reflexive
reachability relation confined to the stage, and it refines as the threshold decreases. -/
theorem t45geo_rips_filtrationLaw {ι : Type*} (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ) :
    FiltrationLaw (fun t => {i | t ≤ g i}) (ripsJoined Dm g δ) where
  antitone := by
    intro s t hst i hi
    exact hst.trans hi
  mem := by
    intro t i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨hgi, ?_⟩
    induction hrt with
    | refl => exact hgi
    | tail _ hbc _ => exact hbc.2.1
  refl := by
    intro t i hi
    exact ⟨hi, Relation.ReflTransGen.refl⟩
  symm := by
    intro t i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨?_, ?_⟩
    · induction hrt with
      | refl => exact hgi
      | tail _ hbc _ => exact hbc.2.1
    · exact t45geo_rtgen_symm (t45geo_RipsRel_symm Dm g δ t) hrt
  trans := by
    intro t i j k hij hjk
    obtain ⟨hgi, hrt1⟩ := hij
    obtain ⟨-, hrt2⟩ := hjk
    exact ⟨hgi, Relation.ReflTransGen.trans hrt1 hrt2⟩
  compat := by
    intro s t hst i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨hst.trans hgi, ?_⟩
    induction hrt with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih => exact ih.tail ⟨hst.trans hab.1, hst.trans hab.2.1, hab.2.2⟩

/-- Any rank function's multiplicity diagram is off the diagonal. -/
theorem t45geo_mult_isDiagramLike (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
  intro p hp
  by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
  · rw [mult, if_pos h1] at hp
    by_cases h2 : p.2 = ⊥
    · rw [if_pos h2] at hp
      rw [h2]
      exact bot_lt_iff_ne_bot.mpr h1.1
    · rw [if_neg h2] at hp
      by_cases h3 : p.2 < p.1
      · exact h3
      · rw [if_neg h3] at hp
        exact (hp rfl).elim
  · rw [mult, if_neg h1] at hp
    exact (hp rfl).elim

/-! ### Helpers for part 6: the support of `ripsDiagram` is finite.

`ripsRank` only depends on the active vertex set `{i | s ≤ g i}` (first argument) and on
the reachability relation `ripsJoined … t` (second argument); both are constant as long as
no value `g i` is crossed.  Hence a point of positive multiplicity must have both extended
coordinates among the (finitely many) sample values `g i`, or second coordinate `⊥`. -/

theorem t45geo6_zero_le (a : ℕ∞) : (0 : ℕ∞) ≤ a := (zero_le : (0 : ℕ∞) ≤ a)

theorem t45geo6_mult_coe_top_eq_zero (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r (((b : ℝ) : EReal), (⊤ : EReal)) = 0 := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (Ne.symm (bot_ne_top : (⊥ : EReal) ≠ ⊤)),
      if_neg (fun h => EReal.coe_ne_top b (le_antisymm le_top h.le))]

theorem t45geo6_mult_coe_bot (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r (((b : ℝ) : EReal), (⊥ : EReal)) =
      ⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ b - ε),
        (r (b - ε) t - r (b + ε) t) := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_pos rfl]
  simp only [EReal.toReal_coe]

theorem t45geo6_mult_coe_coe (r : ℝ → ℝ → ℕ∞) (b d : ℝ) (hbd : d < b) :
    mult r (((b : ℝ) : EReal), ((d : ℝ) : EReal)) =
      ⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo (0 : ℝ) ((b - d) / 2)),
        ((r (b - ε) (d + ε) - r (b + ε) (d + ε)) -
          (r (b - ε) (d - ε) - r (b + ε) (d - ε))) := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (EReal.coe_ne_bot d), if_pos (EReal.coe_lt_coe_iff.mpr hbd)]
  simp only [EReal.toReal_coe]

/-- A finite set of reals avoiding `b` has a positive pointwise lower bound on `|c - b|`. -/
theorem t45geo6_minDist (S : Set ℝ) (b : ℝ) (hS : S.Finite) (hb : b ∉ S) :
    ∃ m > 0, ∀ c ∈ S, m ≤ |c - b| := by
  classical
  by_cases hne : S.Nonempty
  · rcases hne with ⟨c0, hc0⟩
    have hd0 : 0 < |c0 - b| := by
      by_contra hx
      have h0 : |c0 - b| = 0 := le_antisymm (not_lt.mp hx) (abs_nonneg _)
      have h1 : c0 = b := by linarith [abs_eq_zero.mp h0]
      exact hb (h1 ▸ hc0)
    have hTfin : ((fun c : ℝ => 1 / |c - b|) '' S).Finite := Set.Finite.image _ hS
    obtain ⟨M, hM⟩ := bddAbove_def.mp hTfin.bddAbove
    have hMc0 : 1 / |c0 - b| ≤ M := hM _ ⟨c0, hc0, rfl⟩
    have hM0 : 0 < M := lt_of_lt_of_le (one_div_pos.mpr hd0) hMc0
    refine ⟨1 / M, by positivity, fun c hc => ?_⟩
    have hcb : 0 < |c - b| := by
      by_contra hx
      have h0 : |c - b| = 0 := le_antisymm (not_lt.mp hx) (abs_nonneg _)
      have h1 : c = b := by linarith [abs_eq_zero.mp h0]
      exact hb (h1 ▸ hc)
    have hle : 1 / M ≤ 1 / (1 / |c - b|) :=
      one_div_le_one_div_of_le (one_div_pos.mpr hcb) (hM _ ⟨c, hc, rfl⟩)
    rwa [one_div_one_div] at hle
  · exact ⟨1, by positivity, fun c hc => (hne ⟨c, hc⟩).elim⟩

variable {ι : Type*}

/-- If no `g i` lies in `[a, b)` with `a ≤ b`, the two upper level sets coincide. -/
theorem t45geo6_stage_eq (g : ι → ℝ) (a b : ℝ) (hab : a ≤ b)
    (h : ∀ i, ¬(a ≤ g i ∧ g i < b)) : {i | a ≤ g i} = {i | b ≤ g i} := by
  ext i
  apply Iff.intro (fun hai => ?_) (fun hbi => hab.trans hbi)
  by_cases h2 : b ≤ g i
  · exact h2
  · exact absurd ⟨hai, not_le.mp h2⟩ (h i)

/-- `ripsRank` is constant in its first argument while no `g i` is crossed. -/
theorem t45geo6_ripsRank_const_s (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ a b t : ℝ)
    (hab : a ≤ b) (h : ∀ i, ¬(a ≤ g i ∧ g i < b)) :
    ripsRank Dm g δ a t = ripsRank Dm g δ b t := by
  show ((fun x => {y | ripsJoined Dm g δ t x y}) '' {i | a ≤ g i}).encard =
       ((fun x => {y | ripsJoined Dm g δ t x y}) '' {i | b ≤ g i}).encard
  rw [t45geo6_stage_eq g a b hab h]

theorem t45geo6_ripsJoined_congr (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ t₁ t₂ : ℝ)
    (hiff : ∀ i, (t₁ ≤ g i) ↔ (t₂ ≤ g i)) (i j : ι) :
    ripsJoined Dm g δ t₁ i j ↔ ripsJoined Dm g δ t₂ i j := by
  show (t₁ ≤ g i ∧ Relation.ReflTransGen
    (fun x y => t₁ ≤ g x ∧ t₁ ≤ g y ∧ (ripsGraph Dm δ).Adj x y) i j) ↔
    (t₂ ≤ g i ∧ Relation.ReflTransGen
    (fun x y => t₂ ≤ g x ∧ t₂ ≤ g y ∧ (ripsGraph Dm δ).Adj x y) i j)
  refine and_congr (hiff i) ?_
  have heq : (fun x y => t₁ ≤ g x ∧ t₁ ≤ g y ∧ (ripsGraph Dm δ).Adj x y) =
             (fun x y => t₂ ≤ g x ∧ t₂ ≤ g y ∧ (ripsGraph Dm δ).Adj x y) := by
    funext x y; rw [hiff x, hiff y]
  rw [heq]

/-- `ripsRank` is constant in its second argument while no `g i` is crossed. -/
theorem t45geo6_ripsRank_const_t (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ s t₁ t₂ : ℝ)
    (hab : t₁ ≤ t₂) (h : ∀ i, ¬(t₁ ≤ g i ∧ g i < t₂)) :
    ripsRank Dm g δ s t₁ = ripsRank Dm g δ s t₂ := by
  have hiff : ∀ i, (t₁ ≤ g i) ↔ (t₂ ≤ g i) := fun i =>
    ⟨fun hai => by
       by_cases h2 : t₂ ≤ g i
       · exact h2
       · exact absurd ⟨hai, not_le.mp h2⟩ (h i),
     fun hbi => hab.trans hbi⟩
  show ((fun x => {y | ripsJoined Dm g δ t₁ x y}) '' {i | s ≤ g i}).encard =
       ((fun x => {y | ripsJoined Dm g δ t₂ x y}) '' {i | s ≤ g i}).encard
  have hfn : (fun x => {y | ripsJoined Dm g δ t₁ x y}) =
            (fun x => {y | ripsJoined Dm g δ t₂ x y}) := by
    funext x; ext y; exact t45geo6_ripsJoined_congr Dm g δ t₁ t₂ hiff x y
  rw [hfn]

/-- A small radius `ε < u` around `b` avoiding all values of `g`. -/
theorem t45geo6_avoid (g : ι → ℝ) (b u m : ℝ) (hm : 0 < m) (hu : 0 < u)
    (hle : ∀ i, m ≤ |g i - b|) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) u, ∀ i, ¬(b - ε ≤ g i ∧ g i < b + ε) := by
  refine ⟨min m u / 2, ⟨by positivity, ?_⟩, ?_⟩
  · have h1 : min m u ≤ u := min_le_right _ _
    have h2 : 0 < min m u := lt_min hm hu
    linarith
  · intro i ⟨h1, h2⟩
    have hεm : min m u / 2 < m := by
      have h3 : min m u ≤ m := min_le_left _ _
      have h4 : 0 < min m u := lt_min hm hu
      linarith
    have habs : |g i - b| ≤ min m u / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have := hle i
    linarith

/-- Every point of positive multiplicity of a Rips diagram has both extended coordinates
among the sample values (second coordinate possibly `⊥`). -/
theorem t45geo6_rips_mult_support [Fintype ι] (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ)
    (p : EReal × EReal) (hp : mult (ripsRank Dm g δ) p ≠ 0) :
    p.1 ∈ Set.range (fun i => ((g i : ℝ) : EReal)) ∧
      (p.2 ∈ Set.range (fun i => ((g i : ℝ) : EReal)) ∨ p.2 = ⊥) := by
  classical
  have hSfin : (Set.range g).Finite := Set.finite_range g
  obtain ⟨b, d⟩ := p
  by_cases hb1 : b = ⊥
  · exfalso; simp [mult, hb1] at hp
  by_cases hb2 : b = ⊤
  · exfalso; simp [mult, hb2] at hp
  obtain ⟨br, rfl⟩ : ∃ br : ℝ, b = ((br : ℝ) : EReal) :=
    ⟨b.toReal, (EReal.coe_toReal hb2 hb1).symm⟩
  by_cases hd1 : d = ⊥
  · subst hd1
    refine ⟨?_, Or.inr rfl⟩
    by_contra hbS
    have hbS' : br ∉ Set.range g := fun ⟨i, hi⟩ => hbS ⟨i, by simp [hi]⟩
    obtain ⟨m, hm, hle⟩ := t45geo6_minDist (Set.range g) br hSfin hbS'
    obtain ⟨ε, ⟨hεpos, _⟩, hnc⟩ :=
      t45geo6_avoid g br 1 m hm one_pos (fun i => hle _ (Set.mem_range_self i))
    have hconst : ∀ t, ripsRank Dm g δ (br - ε) t = ripsRank Dm g δ (br + ε) t :=
      fun t => t45geo6_ripsRank_const_s Dm g δ (br - ε) (br + ε) t (by linarith) hnc
    have h0 : mult (ripsRank Dm g δ) (((br : ℝ) : EReal), (⊥ : EReal)) = 0 := by
      rw [t45geo6_mult_coe_bot]
      refine le_antisymm ?_
        (le_iInf fun η => le_iInf fun _ => le_iInf fun t => le_iInf fun _ => t45geo6_zero_le _)
      have hz : ripsRank Dm g δ (br - ε) (br - ε) - ripsRank Dm g δ (br + ε) (br - ε) = 0 := by
        rw [hconst (br - ε)]; exact tsub_self _
      have hval : (⨅ (t : ℝ) (_ : t ≤ br - ε),
          ripsRank Dm g δ (br - ε) t - ripsRank Dm g δ (br + ε) t) = 0 :=
        le_antisymm (iInf_le_of_le (br - ε) (iInf_le_of_le (le_refl _) (le_of_eq hz)))
          (le_iInf fun t => le_iInf fun _ => t45geo6_zero_le _)
      exact iInf_le_of_le ε (iInf_le_of_le hεpos (le_of_eq hval))
    exact hp h0
  by_cases hd2 : d = ⊤
  · exfalso; subst hd2; rw [t45geo6_mult_coe_top_eq_zero] at hp; exact hp rfl
  obtain ⟨dr, rfl⟩ : ∃ dr : ℝ, d = ((dr : ℝ) : EReal) :=
    ⟨d.toReal, (EReal.coe_toReal hd2 hd1).symm⟩
  by_cases hdb : dr < br
  · refine ⟨?_, Or.inl ?_⟩
    · by_contra hbS
      have hbS' : br ∉ Set.range g := fun ⟨i, hi⟩ => hbS ⟨i, by simp [hi]⟩
      obtain ⟨m, hm, hle⟩ := t45geo6_minDist (Set.range g) br hSfin hbS'
      obtain ⟨ε, ⟨hεpos, hεu⟩, hnc⟩ :=
        t45geo6_avoid g br ((br - dr) / 2) m hm (by linarith)
          (fun i => hle _ (Set.mem_range_self i))
      have hmem : ε ∈ Set.Ioo (0 : ℝ) ((br - dr) / 2) := ⟨hεpos, hεu⟩
      have hconst : ∀ t, ripsRank Dm g δ (br - ε) t = ripsRank Dm g δ (br + ε) t :=
        fun t => t45geo6_ripsRank_const_s Dm g δ (br - ε) (br + ε) t (by linarith) hnc
      have h0 : mult (ripsRank Dm g δ) (((br : ℝ) : EReal), ((dr : ℝ) : EReal)) = 0 := by
        rw [t45geo6_mult_coe_coe _ br dr hdb]
        refine le_antisymm ?_
          (le_iInf fun η => le_iInf fun _ => t45geo6_zero_le _)
        have hz : (ripsRank Dm g δ (br - ε) (dr + ε) - ripsRank Dm g δ (br + ε) (dr + ε)) -
            (ripsRank Dm g δ (br - ε) (dr - ε) - ripsRank Dm g δ (br + ε) (dr - ε)) = 0 := by
          rw [hconst (dr + ε), hconst (dr - ε)]; simp [tsub_self]
        exact iInf_le_of_le ε (iInf_le_of_le hmem (le_of_eq hz))
      exact hp h0
    · by_contra hdS
      have hdS' : dr ∉ Set.range g := fun ⟨i, hi⟩ => hdS ⟨i, by simp [hi]⟩
      obtain ⟨m, hm, hle⟩ := t45geo6_minDist (Set.range g) dr hSfin hdS'
      obtain ⟨ε, ⟨hεpos, hεu⟩, hnc⟩ :=
        t45geo6_avoid g dr ((br - dr) / 2) m hm (by linarith)
          (fun i => hle _ (Set.mem_range_self i))
      have hmem : ε ∈ Set.Ioo (0 : ℝ) ((br - dr) / 2) := ⟨hεpos, hεu⟩
      have hconst : ∀ s, ripsRank Dm g δ s (dr - ε) = ripsRank Dm g δ s (dr + ε) :=
        fun s => t45geo6_ripsRank_const_t Dm g δ s (dr - ε) (dr + ε) (by linarith) hnc
      have h0 : mult (ripsRank Dm g δ) (((br : ℝ) : EReal), ((dr : ℝ) : EReal)) = 0 := by
        rw [t45geo6_mult_coe_coe _ br dr hdb]
        refine le_antisymm ?_
          (le_iInf fun η => le_iInf fun _ => t45geo6_zero_le _)
        have hz : (ripsRank Dm g δ (br - ε) (dr + ε) - ripsRank Dm g δ (br + ε) (dr + ε)) -
            (ripsRank Dm g δ (br - ε) (dr - ε) - ripsRank Dm g δ (br + ε) (dr - ε)) = 0 := by
          rw [hconst (br - ε), hconst (br + ε)]; simp [tsub_self]
        exact iInf_le_of_le ε (iInf_le_of_le hmem (le_of_eq hz))
      exact hp h0
  · exfalso; simp [mult, EReal.coe_ne_bot, EReal.coe_ne_top, EReal.coe_lt_coe_iff, hdb] at hp

/-- Part 6: the support of the Rips persistence diagram is finite (the vertex type is finite). -/
theorem t45geo6_rips_support_finite [Fintype ι] (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ) :
    {p : EReal × EReal | (ripsDiagram Dm g δ) p ≠ 0}.Finite := by
  have hTfin : (Set.range (fun i => ((g i : ℝ) : EReal))).Finite := Set.finite_range _
  have hUfin : (Set.range (fun i => ((g i : ℝ) : EReal)) ∪ {(⊥ : EReal)}).Finite :=
    hTfin.union (Set.finite_singleton _)
  refine Set.Finite.subset (hTfin.prod hUfin) ?_
  intro p hp
  obtain ⟨h1, h2⟩ := t45geo6_rips_mult_support Dm g δ p hp
  obtain ⟨b, d⟩ := p
  refine Set.mem_prod.mpr ⟨h1, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · refine Or.inr ?_
    rw [h2]; exact Set.mem_singleton _

/-! ### Helpers for part 5: the support of `diagram0 f` is finite (tameness). -/

/-- **C1'**: for `t ≤ u ≤ v` with no critical values in `[u, v]`, the rank's first argument may
be moved from `u` to `v` (P1 upgrades `F^u`-points to `F^v`-points without changing components
at level `t`, because `JoinedIn (𝔽^u)` implies `JoinedIn (𝔽^t)` for `t ≤ u`). -/
theorem t45geo5_superRank_const_s {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    {t u v : ℝ} (htu : t ≤ u) (huv : u ≤ v)
    (hP1 : ∀ x ∈ superlevel f u, ∃ y ∈ superlevel f v, JoinedIn (superlevel f u) x y) :
    superRank f u t = superRank f v t := by
  show ((fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f u).encard =
       ((fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f v).encard
  have himg : (fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f u =
              (fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f v := by
    apply Set.Subset.antisymm
    · rintro S ⟨x, hx, rfl⟩
      obtain ⟨y, hyv, hj⟩ := hP1 x hx
      refine ⟨y, hyv, ?_⟩
      ext z
      exact ⟨fun h => JoinedIn.trans (JoinedIn.mono hj (fun w hw => htu.trans hw)) h,
             fun h => JoinedIn.trans (JoinedIn.symm (JoinedIn.mono hj (fun w hw => htu.trans hw))) h⟩
    · rintro S ⟨x, hx, rfl⟩
      exact ⟨x, huv.trans hx, rfl⟩
  rw [himg]

/-- **C2'**: for `u ≤ v ≤ s` with no critical values in `[u, v]`, the rank's second argument may
be moved from `u` to `v`: the map "component of `x` at level `u` ↦ component of `x` at level `v`"
on points of `𝔽^s` is a well-defined bijection between the two families of components, using
P2 (components do not merge going down) and `JoinedIn.mono`. -/
theorem t45geo5_superRank_const_t {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    {u v s : ℝ} (huv : u ≤ v) (hvs : v ≤ s)
    (hP2 : ∀ y ∈ superlevel f v, ∀ y' ∈ superlevel f v,
      JoinedIn (superlevel f u) y y' → JoinedIn (superlevel f v) y y') :
    superRank f s u = superRank f s v := by
  classical
  show ((fun x => {y | JoinedIn (superlevel f u) x y}) '' superlevel f s).encard =
       ((fun x => {y | JoinedIn (superlevel f v) x y}) '' superlevel f s).encard
  have hvu : superlevel f v ⊆ superlevel f u := fun _ hw => huv.trans hw
  have hsm : superlevel f s ⊆ superlevel f v := fun _ hw => hvs.trans hw
  -- well-definedness of `x ↦ C_v x` on the fibers of `C_u` (uses P2)
  have hwd : ∀ x₁ ∈ superlevel f s, ∀ x₂ ∈ superlevel f s,
      {y | JoinedIn (superlevel f u) x₁ y} = {y | JoinedIn (superlevel f u) x₂ y} →
      {y | JoinedIn (superlevel f v) x₁ y} = {y | JoinedIn (superlevel f v) x₂ y} := by
    intro x₁ hx₁ x₂ hx₂ heq
    have hj : JoinedIn (superlevel f u) x₂ x₁ := by
      have hmem : x₁ ∈ {y | JoinedIn (superlevel f u) x₂ y} := by
        rw [← heq]
        exact JoinedIn.refl (hvu (hsm hx₁))
      exact hmem
    have hjv : JoinedIn (superlevel f v) x₂ x₁ := hP2 x₂ (hsm hx₂) x₁ (hsm hx₁) hj
    ext z
    exact ⟨fun h => JoinedIn.trans hjv h, fun h => JoinedIn.trans (JoinedIn.symm hjv) h⟩
  -- the canonical bijection `C_u x ↦ C_v x`, made via a chosen representative
  refine Set.encard_congr (Equiv.ofBijective
    (fun a : {T : Set X // T ∈ (fun x => {y | JoinedIn (superlevel f u) x y}) '' superlevel f s} =>
      ⟨(fun x => {y | JoinedIn (superlevel f v) x y}) (Classical.choose a.2),
        ⟨Classical.choose a.2, (Classical.choose_spec a.2).1, rfl⟩⟩) ?_)
  constructor
  · -- injective (mono suffices)
    intro a₁ a₂ hEq
    have hvv : (fun x => {y | JoinedIn (superlevel f v) x y})
        (Classical.choose a₁.2) =
        (fun x => {y | JoinedIn (superlevel f v) x y})
          (Classical.choose a₂.2) := congrArg Subtype.val hEq
    have hc₁ : Classical.choose a₁.2 ∈ superlevel f s :=
      (Classical.choose_spec a₁.2).1
    have hjv : JoinedIn (superlevel f v)
        (Classical.choose a₂.2) (Classical.choose a₁.2) := by
      have h1 : Classical.choose a₁.2 ∈
          (fun x => {y | JoinedIn (superlevel f v) x y}) (Classical.choose a₂.2) := by
        rw [← hvv]
        exact JoinedIn.refl (hsm hc₁)
      exact h1
    have hju : JoinedIn (superlevel f u)
        (Classical.choose a₂.2) (Classical.choose a₁.2) :=
      JoinedIn.mono hjv hvu
    have hCu : {y | JoinedIn (superlevel f u) (Classical.choose a₁.2) y} =
               {y | JoinedIn (superlevel f u) (Classical.choose a₂.2) y} := by
      ext z
      exact ⟨fun h => JoinedIn.trans hju h,
             fun h => JoinedIn.trans (JoinedIn.symm hju) h⟩
    apply Subtype.ext
    rw [← (Classical.choose_spec a₁.2).2, ← (Classical.choose_spec a₂.2).2]
    exact hCu
  · -- surjective
    rintro ⟨T, hT⟩
    obtain ⟨x, hx, rfl⟩ := hT
    have hP : (fun x => {y | JoinedIn (superlevel f u) x y}) x ∈
        (fun x => {y | JoinedIn (superlevel f u) x y}) '' superlevel f s :=
      ⟨x, hx, rfl⟩
    have hspec := Classical.choose_spec hP
    refine ⟨⟨(fun x => {y | JoinedIn (superlevel f u) x y}) x, hP⟩, ?_⟩
    apply Subtype.ext
    exact hwd (Classical.choose hP) hspec.1 x hx hspec.2

/-- A small radius `ε < u` around `b` avoiding all values of the finite set `T`. -/
theorem t45geo5_avoid (T : Finset ℝ) (b u m : ℝ) (hm : 0 < m) (hu : 0 < u)
    (hle : ∀ w ∈ T, m ≤ |w - b|) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) u, ∀ w ∈ T, ¬(b - ε ≤ w ∧ w ≤ b + ε) := by
  refine ⟨min m u / 2, ⟨by positivity, ?_⟩, ?_⟩
  · have h1 : min m u ≤ u := min_le_right _ _
    have h2 : 0 < min m u := lt_min hm hu
    linarith
  · intro w hw ⟨h1, h2⟩
    have hεm : min m u / 2 < m := by
      have h3 : min m u ≤ m := min_le_left _ _
      have h4 : 0 < min m u := lt_min hm hu
      linarith
    have habs : |w - b| ≤ min m u / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := hle w hw
    linarith

/-- Reformulate the "no critical value in `[a, b']`" clause for `Finset` membership. -/
theorem t45geo5_avoid_iff {T : Finset ℝ} {a b' : ℝ}
    (hnc : ∀ w ∈ T, ¬(a ≤ w ∧ w ≤ b')) : ∀ w ∈ T, w < a ∨ b' < w := by
  intro w hw
  rcases not_and_or.mp (hnc w hw) with h | h
  · exact Or.inl (lt_of_not_ge h)
  · exact Or.inr (lt_of_not_ge h)

/-- Every point of positive multiplicity of `D₀f` has both extended coordinates among the
critical values `T` (the second coordinate possibly `⊥`). -/
theorem t45geo5_super_mult_support {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (T : Finset ℝ)
    (hTame : ∀ t s : ℝ, t ≤ s → (∀ w ∈ T, w < t ∨ s < w) →
      (∀ x ∈ superlevel f t, ∃ y ∈ superlevel f s, JoinedIn (superlevel f t) x y) ∧
      (∀ y ∈ superlevel f s, ∀ y' ∈ superlevel f s,
        JoinedIn (superlevel f t) y y' → JoinedIn (superlevel f s) y y'))
    (p : EReal × EReal) (hp : mult (superRank f) p ≠ 0) :
    p.1 ∈ (fun w : ℝ => ((w : ℝ) : EReal)) '' (T : Set ℝ) ∧
      (p.2 ∈ (fun w : ℝ => ((w : ℝ) : EReal)) '' (T : Set ℝ) ∨ p.2 = ⊥) := by
  classical
  have hTfin : (T : Set ℝ).Finite := T.finite_toSet
  obtain ⟨b, d⟩ := p
  by_cases hb1 : b = ⊥
  · exfalso; simp [mult, hb1] at hp
  by_cases hb2 : b = ⊤
  · exfalso; simp [mult, hb2] at hp
  obtain ⟨br, rfl⟩ : ∃ br : ℝ, b = ((br : ℝ) : EReal) :=
    ⟨b.toReal, (EReal.coe_toReal hb2 hb1).symm⟩
  by_cases hd1 : d = ⊥
  · subst hd1
    refine ⟨?_, Or.inr rfl⟩
    by_contra hcon
    have hbT : br ∉ (T : Set ℝ) := by
      intro hmem; exact hcon ⟨br, hmem, rfl⟩
    obtain ⟨m, hm, hle⟩ := t45geo6_minDist (T : Set ℝ) br hTfin hbT
    obtain ⟨ε, ⟨hεpos, _⟩, hnc⟩ := t45geo5_avoid T br 1 m hm one_pos (fun w hw => hle _ hw)
    have hnc' := t45geo5_avoid_iff hnc
    have hP1 := (hTame (br - ε) (br + ε) (by linarith) hnc').1
    have hconst : ∀ t ≤ br - ε, superRank f (br - ε) t = superRank f (br + ε) t :=
      fun t ht => t45geo5_superRank_const_s ht (by linarith) hP1
    have h0 : mult (superRank f) (((br : ℝ) : EReal), (⊥ : EReal)) = 0 := by
      rw [t45geo6_mult_coe_bot]
      refine le_antisymm ?_
        (le_iInf fun η => le_iInf fun _ => le_iInf fun t => le_iInf fun _ => t45geo6_zero_le _)
      have hz : superRank f (br - ε) (br - ε) - superRank f (br + ε) (br - ε) = 0 := by
        rw [hconst (br - ε) (le_refl _)]
        exact tsub_self _
      have hval : (⨅ (t : ℝ) (_ : t ≤ br - ε),
          superRank f (br - ε) t - superRank f (br + ε) t) = 0 :=
        le_antisymm (iInf_le_of_le (br - ε) (iInf_le_of_le (le_refl _) (le_of_eq hz)))
          (le_iInf fun t => le_iInf fun _ => t45geo6_zero_le _)
      exact iInf_le_of_le ε (iInf_le_of_le hεpos (le_of_eq hval))
    exact hp h0
  by_cases hd2 : d = ⊤
  · exfalso; subst hd2; rw [t45geo6_mult_coe_top_eq_zero] at hp; exact hp rfl
  obtain ⟨dr, rfl⟩ : ∃ dr : ℝ, d = ((dr : ℝ) : EReal) :=
    ⟨d.toReal, (EReal.coe_toReal hd2 hd1).symm⟩
  by_cases hdb : dr < br
  · refine ⟨?_, Or.inl ?_⟩
    · by_contra hcon
      have hbT : br ∉ (T : Set ℝ) := by
        intro hmem; exact hcon ⟨br, hmem, rfl⟩
      obtain ⟨m, hm, hle⟩ := t45geo6_minDist (T : Set ℝ) br hTfin hbT
      obtain ⟨ε, ⟨hεpos, hεu⟩, hnc⟩ :=
        t45geo5_avoid T br ((br - dr) / 2) m hm (by linarith) (fun w hw => hle _ hw)
      have hnc' := t45geo5_avoid_iff hnc
      have hmem : ε ∈ Set.Ioo (0 : ℝ) ((br - dr) / 2) := ⟨hεpos, hεu⟩
      have hP1 := (hTame (br - ε) (br + ε) (by linarith) hnc').1
      have hconst : ∀ t ≤ br - ε, superRank f (br - ε) t = superRank f (br + ε) t :=
        fun t ht => t45geo5_superRank_const_s ht (by linarith) hP1
      have h0 : mult (superRank f) (((br : ℝ) : EReal), ((dr : ℝ) : EReal)) = 0 := by
        rw [t45geo6_mult_coe_coe _ br dr hdb]
        refine le_antisymm ?_ (le_iInf fun η => le_iInf fun _ => t45geo6_zero_le _)
        have hz : (superRank f (br - ε) (dr + ε) - superRank f (br + ε) (dr + ε)) -
            (superRank f (br - ε) (dr - ε) - superRank f (br + ε) (dr - ε)) = 0 := by
          rw [hconst (dr + ε) (by linarith), hconst (dr - ε) (by linarith)]
          simp [tsub_self]
        exact iInf_le_of_le ε (iInf_le_of_le hmem (le_of_eq hz))
      exact hp h0
    · by_contra hcon
      have hdT : dr ∉ (T : Set ℝ) := by
        intro hmem; exact hcon ⟨dr, hmem, rfl⟩
      obtain ⟨m, hm, hle⟩ := t45geo6_minDist (T : Set ℝ) dr hTfin hdT
      obtain ⟨ε, ⟨hεpos, hεu⟩, hnc⟩ :=
        t45geo5_avoid T dr ((br - dr) / 2) m hm (by linarith) (fun w hw => hle _ hw)
      have hnc' := t45geo5_avoid_iff hnc
      have hmem : ε ∈ Set.Ioo (0 : ℝ) ((br - dr) / 2) := ⟨hεpos, hεu⟩
      have hP2 := (hTame (dr - ε) (dr + ε) (by linarith) hnc').2
      have hconst : ∀ s, dr + ε ≤ s → superRank f s (dr - ε) = superRank f s (dr + ε) :=
        fun s hs => t45geo5_superRank_const_t (by linarith) hs hP2
      have h0 : mult (superRank f) (((br : ℝ) : EReal), ((dr : ℝ) : EReal)) = 0 := by
        rw [t45geo6_mult_coe_coe _ br dr hdb]
        refine le_antisymm ?_ (le_iInf fun η => le_iInf fun _ => t45geo6_zero_le _)
        have hz : (superRank f (br - ε) (dr + ε) - superRank f (br + ε) (dr + ε)) -
            (superRank f (br - ε) (dr - ε) - superRank f (br + ε) (dr - ε)) = 0 := by
          rw [hconst (br - ε) (by linarith), hconst (br + ε) (by linarith)]
          simp [tsub_self]
        exact iInf_le_of_le ε (iInf_le_of_le hmem (le_of_eq hz))
      exact hp h0
  · exfalso; simp [mult, EReal.coe_ne_bot, EReal.coe_ne_top, EReal.coe_lt_coe_iff, hdb] at hp

/-- Part 5: the support of the superlevel persistence diagram is finite (tameness). -/
theorem t45geo5_super_support_finite {X : Type*} [TopologicalSpace X] {f : X → ℝ} (htame : IsTame0 f) :
    {p : EReal × EReal | (diagram0 f) p ≠ 0}.Finite := by
  obtain ⟨-, ⟨T, hTame⟩, -⟩ := htame
  have hTfin : ((fun w : ℝ => ((w : ℝ) : EReal)) '' (T : Set ℝ)).Finite :=
    Set.Finite.image _ T.finite_toSet
  have hUfin : ((fun w : ℝ => ((w : ℝ) : EReal)) '' (T : Set ℝ) ∪ {(⊥ : EReal)}).Finite :=
    hTfin.union (Set.finite_singleton _)
  refine Set.Finite.subset (hTfin.prod hUfin) ?_
  intro p hp
  obtain ⟨h1, h2⟩ := t45geo5_super_mult_support T hTame p hp
  obtain ⟨b, d⟩ := p
  refine Set.mem_prod.mpr ⟨h1, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · refine Or.inr ?_
    rw [h2]; exact Set.mem_singleton _


/-! ### Helpers for part 7: the geometric core (`lift`, discrete chains both ways). -/

namespace T45Geo7

theorem isom_dist_eq {X : Type*} [MetricSpace X] {d : ℝ}
    (γ : Set.Icc (0 : ℝ) d → X) (hiso : Isometry γ) (x y : Set.Icc (0 : ℝ) d) :
    dist (γ x) (γ y) = dist x y := by
  have h := hiso x y
  rw [edist_dist, edist_dist] at h
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg).mp h

theorem lift {X : Type*} [MetricSpace X] (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (a b : X) (t : ℝ)
    (hd : ENNReal.ofReal (dist a b) < convexityRadius X)
    (ha : t + c * dist a b ≤ f a) (hb : t + c * dist a b ≤ f b) :
    JoinedIn (superlevel f t) a b := by
  classical
  have h1 : ENNReal.ofReal (dist a b) < convexityRadiusAt a :=
    lt_of_lt_of_le hd (iInf_le (fun x : X => convexityRadiusAt x) a)
  obtain ⟨r, hr0, hrsc, hrd⟩ : ∃ r, 0 ≤ r ∧ IsStronglyConvexBall a r ∧ dist a b < r := by
    by_contra hx
    push_neg at hx
    apply absurd h1
    rw [not_lt]
    refine iSup_le_iff.mpr (fun s => ?_)
    refine iSup_le_iff.mpr (fun hs0 => ?_)
    refine iSup_le_iff.mpr (fun hsc => ?_)
    exact ENNReal.ofReal_le_ofReal (hx s hs0 hsc)
  have ha_mem : a ∈ Metric.closedBall a r :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr0)
  have hb_mem : b ∈ Metric.closedBall a r :=
    Metric.mem_closedBall.mpr (by rw [dist_comm]; exact le_of_lt hrd)
  obtain ⟨γ, hγ, -⟩ := (hrsc a ha_mem b hb_mem).1
  rcases hγ with ⟨hiso, hγ0, hγd⟩
  have hd0 : (0 : ℝ) ≤ dist a b := dist_nonneg
  have hmul : Continuous (fun u : unitInterval => ((u : ℝ) * dist a b : ℝ)) :=
    Continuous.mul_const continuous_subtype_val (dist a b)
  have hmem : ∀ u : unitInterval, ((u : ℝ) * dist a b) ∈ Set.Icc (0 : ℝ) (dist a b) := by
    intro u
    refine ⟨by nlinarith [u.2.1, hd0], ?_⟩
    nlinarith [u.2.1, u.2.2, hd0]
  have hgcont : Continuous (fun u : unitInterval =>
      (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b))) :=
    Continuous.subtype_mk hmul hmem
  have hcont : Continuous (fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩)) :=
    hiso.continuous.comp hgcont
  have hsrc : (fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩)) 0 = a := by
    have e0 : (⟨((0 : unitInterval) : ℝ) * dist a b, hmem 0⟩ : Set.Icc (0 : ℝ) (dist a b))
        = ⟨(0 : ℝ), le_refl 0, dist_nonneg⟩ := Subtype.ext (by simp)
    show γ (⟨((0 : unitInterval) : ℝ) * dist a b, hmem 0⟩) = a
    rw [e0, hγ0]
  have htgt : (fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩)) 1 = b := by
    have e1 : (⟨((1 : unitInterval) : ℝ) * dist a b, hmem 1⟩ : Set.Icc (0 : ℝ) (dist a b))
        = ⟨dist a b, dist_nonneg, le_refl (dist a b)⟩ := Subtype.ext (by simp)
    show γ (⟨((1 : unitInterval) : ℝ) * dist a b, hmem 1⟩) = b
    rw [e1, hγd]
  refine ⟨⟨⟨fun u : unitInterval => γ (⟨(u : ℝ) * dist a b, hmem u⟩), hcont⟩, hsrc, htgt⟩, fun u => ?_⟩
  show t ≤ f (γ (⟨(u : ℝ) * dist a b, hmem u⟩))
  have hu : (0 : ℝ) ≤ (u : ℝ) := u.2.1
  have hdist : dist (γ (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b))) a
      = (u : ℝ) * dist a b := by
    have h0 : dist (γ (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b)))
        (γ (⟨(0 : ℝ), le_refl 0, dist_nonneg⟩ : Set.Icc (0 : ℝ) (dist a b)))
        = dist (⟨(u : ℝ) * dist a b, hmem u⟩ : Set.Icc (0 : ℝ) (dist a b))
          (⟨(0 : ℝ), le_refl 0, dist_nonneg⟩ : Set.Icc (0 : ℝ) (dist a b)) :=
      isom_dist_eq γ hiso _ _
    rw [hγ0] at h0
    rw [h0, Subtype.dist_eq, Real.dist_eq]
    simp only [Subtype.coe_mk, sub_zero]
    rw [abs_of_nonneg (mul_nonneg hu hd0)]
  have hb1 : |f (γ (⟨(u : ℝ) * dist a b, hmem u⟩)) - f a| ≤ c * dist (γ (⟨(u : ℝ) * dist a b, hmem u⟩)) a :=
    hLip _ _
  rw [hdist] at hb1
  have hud : (u : ℝ) * dist a b ≤ dist a b := by
    nlinarith [u.2.1, u.2.2, hd0]
  have hcle : c * ((u : ℝ) * dist a b) ≤ c * dist a b :=
    mul_le_mul_of_nonneg_left hud hc
  have hlow := (abs_le.mp hb1).1
  linarith

/-! ### Direction A: discrete Rips chains in `L^{t+cδ}` lift to `F^t`-joinedness. -/

/-- A single Rips-adjacent pair with grades `≥ t + cδ` lifts to an `F^t`-path. -/
theorem step_super {X : Type*} [MetricSpace X] {ι : Type*} (coe : ι → X) (Dm : ι → ι → ℝ)
    (hDm : ∀ a b, Dm a b = dist (coe a) (coe b))
    (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (δ t : ℝ) (hconvρ : ENNReal.ofReal δ < convexityRadius X) (a b : ι)
    (h1 : t + c * δ ≤ f (coe a)) (h2 : t + c * δ ≤ f (coe b))
    (hadj : (ripsGraph Dm δ).Adj a b) :
    JoinedIn (superlevel f t) (coe a) (coe b) := by
  classical
  have hds : Dm a b ≤ δ := by
    have hadj' := (SimpleGraph.fromRel_adj (fun i j => Dm i j ≤ δ) a b).mp hadj
    rcases hadj'.2 with h | h
    · exact h
    · rw [hDm b a, dist_comm, ← hDm a b] at h
      exact h
  have hdist : dist (coe a) (coe b) ≤ δ := by rw [← hDm]; exact hds
  refine lift f c hc hLip (coe a) (coe b) t ?_ ?_ ?_
  · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hdist) hconvρ
  · linarith [mul_le_mul_of_nonneg_left hdist hc]
  · linarith [mul_le_mul_of_nonneg_left hdist hc]

/-- A Rips path in `L^{t+cδ}` from `i` to `j`, starting at grade `≥ t + cδ`, lifts to an
`F^t`-path joining the two sample points. -/
theorem chain_super {X : Type*} [MetricSpace X] {ι : Type*} (coe : ι → X) (Dm : ι → ι → ℝ)
    (hDm : ∀ a b, Dm a b = dist (coe a) (coe b))
    (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (δ t : ℝ) (hδ : 0 < δ) (hconvρ : ENNReal.ofReal δ < convexityRadius X) (i j : ι)
    (h : ripsJoined Dm (fun a => f (coe a)) δ (t + c * δ) i j) :
    JoinedIn (superlevel f t) (coe i) (coe j) := by
  classical
  obtain ⟨hi, hrt⟩ := h
  induction hrt with
  | refl => exact JoinedIn.refl (le_trans (by linarith [mul_nonneg hc hδ.le]) hi)
  | tail hab hbc ih =>
    exact ih.trans
      (step_super coe Dm hDm f c hc hLip δ t hconvρ _ _ hbc.1 hbc.2.1 hbc.2.2)

/-! ### Direction B: `F^{t'}`-joinedness samples down to a Rips chain. -/

theorem stepOrRefl {α : Type*} {r : α → α → Prop} (a b : α) (h : a = b ∨ r a b) :
    Relation.ReflTransGen r a b := by
  rcases h with h | h
  · subst h; exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h

/-- An `F^{t'}`-path between two sample points, with `t' ≥ α`, samples down to a Rips chain in
`L^{t' - cδ/4}` (which the filtration `compat` then lowers to any smaller level). -/
theorem chain_rips {X : Type*} [MetricSpace X] {ι : Type*}
    (coe : ι → X) (Dm : ι → ι → ℝ) (hDm : ∀ a b, Dm a b = dist (coe a) (coe b))
    (g : ι → ℝ) (f : X → ℝ) (hgf : ∀ i, g i = f (coe i))
    (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (δ : ℝ) (hδ : 0 < δ) (t' : ℝ)
    (hsamp : ∀ z : X, t' ≤ f z → ∃ v : ι, dist z (coe v) ≤ δ / 4)
    (x y : ι) (hjoined : JoinedIn (superlevel f t') (coe x) (coe y)) :
    ripsJoined Dm g δ (t' - c * (δ / 4)) x y := by
  classical
  obtain ⟨p, hp⟩ := hjoined
  have hp' : ∀ u : unitInterval, t' ≤ f (p u) := fun u => hp u
  have huc : UniformContinuous ⇑p := CompactSpace.uniformContinuous_of_continuous p.continuous
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨d, hd0, hud⟩ := huc (δ / 4) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd0
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  -- a total sampling function
  obtain ⟨v0, -⟩ : ∃ v : ι, True := by
    obtain ⟨v, -⟩ := hsamp (p 0) (hp' 0); exact ⟨v, trivial⟩
  have htot : ∀ z : X, ∃ v : ι, t' ≤ f z → dist z (coe v) ≤ δ / 4 := by
    intro z
    by_cases hz : t' ≤ f z
    · obtain ⟨v, hv⟩ := hsamp z hz; exact ⟨v, fun _ => hv⟩
    · exact ⟨v0, fun h => absurd h hz⟩
  choose vsamp hvsamp using htot
  -- partition points
  set uu : ℕ → unitInterval := fun k =>
    ⟨((min k N : ℕ) : ℝ) / (N : ℝ), by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]
      exact_mod_cast min_le_right k N⟩ with huudef
  have uu_eq : ∀ k : ℕ, k ≤ N → ((uu k : unitInterval) : ℝ) = (k : ℝ) / (N : ℝ) := by
    intro k hk
    simp only [uu, Subtype.coe_mk]
    rw [min_eq_left hk]
  set w : ℕ → ι := fun k => vsamp (p (uu k)) with hwdef
  -- grades of the chain
  have hwgrade : ∀ k : ℕ, t' - c * (δ / 4) ≤ g (w k) := by
    intro k
    have hz : t' ≤ f (p (uu k)) := hp' (uu k)
    have hdist : dist (p (uu k)) (coe (w k)) ≤ δ / 4 := hvsamp (p (uu k)) hz
    have hb := (abs_le.mp (hLip (coe (w k)) (p (uu k)))).1
    have hmul : c * dist (coe (w k)) (p (uu k)) ≤ c * (δ / 4) :=
      mul_le_mul_of_nonneg_left (by rwa [dist_comm] at hdist) hc
    rw [hgf (w k)]
    linarith
  have hxgrade : t' - c * (δ / 4) ≤ g x := by
    have hx : t' ≤ f (coe x) := by have := hp 0; rwa [p.source] at this
    rw [hgf x]; linarith [hx, mul_nonneg hc (by linarith [hδ] : (0:ℝ) ≤ δ/4)]
  have hygrade : t' - c * (δ / 4) ≤ g y := by
    have hy : t' ≤ f (coe y) := by have := hp 1; rwa [p.target] at this
    rw [hgf y]; linarith [hy, mul_nonneg hc (by linarith [hδ] : (0:ℝ) ≤ δ/4)]
  -- consecutive distances
  have hdist_uu : ∀ k : ℕ, k + 1 ≤ N → dist (uu k) (uu (k + 1)) = 1 / (N : ℝ) := by
    intro k hk1
    have hk : k ≤ N := le_trans (Nat.le_succ k) hk1
    rw [Subtype.dist_eq, Real.dist_eq, uu_eq k hk, uu_eq (k + 1) hk1]
    rw [show (k : ℝ) / (N : ℝ) - ((k + 1 : ℕ) : ℝ) / (N : ℝ) = -(1 / (N : ℝ)) by
      have hc1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hc1]; ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hstepdist : ∀ k : ℕ, k + 1 ≤ N → dist (coe (w k)) (coe (w (k + 1))) ≤ δ := by
    intro k hk1
    have hk : k ≤ N := le_trans (Nat.le_succ k) hk1
    have hlt : dist (uu k) (uu (k + 1)) < d := by
      rw [hdist_uu k hk1, hNdef]; push_cast; exact hn
    have hpdist : dist (p (uu k)) (p (uu (k + 1))) < δ / 4 := hud hlt
    have h1 : dist (coe (w k)) (p (uu k)) ≤ δ / 4 := by
      rw [dist_comm]; exact hvsamp (p (uu k)) (hp' (uu k))
    have h2 : dist (p (uu (k + 1))) (coe (w (k + 1))) ≤ δ / 4 :=
      hvsamp (p (uu (k + 1))) (hp' (uu (k + 1)))
    have := dist_triangle4 (coe (w k)) (p (uu k)) (p (uu (k + 1))) (coe (w (k + 1)))
    linarith [le_of_lt hpdist]
  -- the chain
  have hchain : ∀ k : ℕ, k ≤ N → Relation.ReflTransGen
      (fun a b => t' - c * (δ / 4) ≤ g a ∧ t' - c * (δ / 4) ≤ g b ∧
        (ripsGraph Dm δ).Adj a b) x (w k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine stepOrRefl x (w 0) ?_
      by_cases hxw : x = w 0
      · exact Or.inl hxw
      · refine Or.inr ⟨hxgrade, hwgrade 0, ?_⟩
        refine (SimpleGraph.fromRel_adj (fun i j => Dm i j ≤ δ) x (w 0)).mpr ⟨hxw, Or.inl ?_⟩
        rw [hDm]
        have hd1 : dist (coe x) (coe (w 0)) ≤ δ := by
          have hvs := hvsamp (p (uu 0)) (hp' (uu 0))
          have hpx : p (uu 0) = coe x := by
            have : uu 0 = 0 := Subtype.ext (by rw [uu_eq 0 (Nat.zero_le N)]; simp)
            rw [this, p.source]
          show dist (coe x) (coe (vsamp (p (uu 0)))) ≤ δ
          rw [hpx] at hvs ⊢
          exact le_trans hvs (by linarith [hδ])
        exact hd1
    | succ k ih =>
      intro hk1
      have hk : k ≤ N := Nat.le_of_succ_le hk1
      by_cases heq : w k = w (k + 1)
      · rw [← heq]; exact ih hk
      · refine (ih hk).tail ⟨hwgrade k, hwgrade (k + 1), ?_⟩
        refine (SimpleGraph.fromRel_adj (fun i j => Dm i j ≤ δ) (w k) (w (k + 1))).mpr
          ⟨heq, Or.inl ?_⟩
        rw [hDm]; exact hstepdist k hk1
  -- final step to `y`
  have hfinal : Relation.ReflTransGen
      (fun a b => t' - c * (δ / 4) ≤ g a ∧ t' - c * (δ / 4) ≤ g b ∧
        (ripsGraph Dm δ).Adj a b) (w N) y := by
    refine stepOrRefl (w N) y ?_
    by_cases hyw : w N = y
    · exact Or.inl hyw
    · refine Or.inr ⟨hwgrade N, hygrade, ?_⟩
      refine (SimpleGraph.fromRel_adj (fun i j => Dm i j ≤ δ) (w N) y).mpr ⟨hyw, Or.inl ?_⟩
      rw [hDm]
      have hvs := hvsamp (p (uu N)) (hp' (uu N))
      have hpN : p (uu N) = coe y := by
        have : uu N = 1 := Subtype.ext (by rw [uu_eq N (le_refl N)]; exact div_self (ne_of_gt hNpos))
        rw [this, p.target]
      show dist (coe (vsamp (p (uu N)))) (coe y) ≤ δ
      rw [hpN] at hvs ⊢
      rw [dist_comm] at hvs
      exact le_trans hvs (by linarith [hδ])
  exact ⟨hxgrade, (hchain N (le_refl N)).trans hfinal⟩

end T45Geo7

/-! # Theorem 4.5 (geometric part, corrected) — the interleaving between the superlevel-set
filtration of `f` and the upper-star Rips filtration of the sample `L`.

Skeleton phase: the seven conjuncts are named `have` steps; parts 1–6 are filled first,
part 7 (the box-expansion rank inequalities with `ε = c * δ`) is the hard geometric core
(paper [6, §3.1], pp. 23–25). -/

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X]
    (hconv : 0 < convexityRadius X)
    (L : Finset X) (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (htame : IsTame0 f)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4)) :
    FiltrationLaw (superlevel f) (fun t => JoinedIn (superlevel f t)) ∧
    FiltrationLaw (fun t => {i | t ≤ (fun x : L => f x) i})
      (ripsJoined (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) ∧
    IsDiagramLike (diagram0 f) ∧
    IsDiagramLike (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) ∧
    {p : EReal × EReal | (diagram0 f) p ≠ 0}.Finite ∧
    {p : EReal × EReal |
        (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) p ≠ 0}.Finite ∧
    (∀ s t : ℝ, t + 2 * (c * δ) ≤ s → α ≤ t →
       superRank f s t ≤
         ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ (s - c * δ) (t + c * δ) ∧
         ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ s t ≤
           superRank f (s - c * δ) (t + c * δ)) := by
  -- Part 1: the superlevel filtration is a genuine filtration (path-component structure).
  have h1 : FiltrationLaw (superlevel f) (fun t => JoinedIn (superlevel f t)) :=
    t45geo_super_filtrationLaw f
  -- Part 2: the upper-star Rips filtration is a genuine filtration (graph-component structure).
  have h2 : FiltrationLaw (fun t => {i | t ≤ (fun x : L => f x) i})
      (ripsJoined (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) :=
    t45geo_rips_filtrationLaw (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ
  -- Part 3: `D₀f` is a diagram off the diagonal.
  have h3 : IsDiagramLike (diagram0 f) := by
    show IsDiagramLike (mult (superRank f))
    exact t45geo_mult_isDiagramLike (superRank f)
  -- Part 4: `D₀𝓡` is a diagram off the diagonal.
  have h4 : IsDiagramLike (ripsDiagram (fun x y : L => dist (x : X) (y : X))
      (fun x : L => f x) δ) := by
    show IsDiagramLike (mult (ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ))
    exact t45geo_mult_isDiagramLike
      (ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ)
  -- Part 5: `D₀f` has finite support (tameness).
  have h5 : {p : EReal × EReal | (diagram0 f) p ≠ 0}.Finite :=
    t45geo5_super_support_finite htame
  -- Part 6: `D₀𝓡` has finite support (finiteness of the vertex set `L`).
  have h6 : {p : EReal × EReal |
      (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) p ≠ 0}.Finite :=
    t45geo6_rips_support_finite
      (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
  -- Part 7: the box-expansion rank inequalities, ε = c · δ.
  have h7 : ∀ s t : ℝ, t + 2 * (c * δ) ≤ s → α ≤ t →
      superRank f s t ≤
        ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ
          (s - c * δ) (t + c * δ) ∧
      ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ s t ≤
        superRank f (s - c * δ) (t + c * δ) := by
    intro s t hst2 hat
    set ε : ℝ := c * δ with hεdef
    have hε0 : 0 ≤ ε := by rw [hεdef]; exact mul_nonneg hc hδ.le
    have hεδ : c * (δ / 4) ≤ ε := by rw [hεdef]; nlinarith [mul_nonneg hc hδ.le]
    have hαs : α ≤ s := by linarith [hat, hst2, hε0]
    -- Direction 1: every path-component of `𝔽^t` meeting `𝔽^s` carries a Rips component of
    -- `L^{t+ε}` meeting `L^{s-ε}`, injectively.
    have hdir1 : superRank f s t ≤
        ripsRank (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ (s - ε) (t + ε) := by
      classical
      show ((fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f s).encard ≤
           ((fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ (t + ε) i j}) ''
             {i : ↥L | s - ε ≤ (fun x : ↥L => f x) i}).encard
      have hchoose : ∀ a : {S : Set X // S ∈ (fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f s},
          ∃ x : X, x ∈ superlevel f s ∧
            (fun x => {y | JoinedIn (superlevel f t) x y}) x = (a : Set X) :=
        fun a => a.2
      choose xval hxval using hchoose
      have hxα : ∀ a, xval a ∈ superlevel f α :=
        fun a => h1.antitone hαs (hxval a).1
      have hchoose2 : ∀ a : {S : Set X // S ∈ (fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f s},
          ∃ v : X, v ∈ (L : Set X) ∧ dist (xval a) v ≤ δ / 4 :=
        fun a => hL (xval a) (hxα a)
      choose vlast hvprop using hchoose2
      have hvhi : ∀ a, t + ε ≤ f (vlast a) := by
        intro a
        have hb := (abs_le.mp (hLip (vlast a) (xval a))).1
        have hcd : c * dist (vlast a) (xval a) ≤ c * (δ / 4) :=
          mul_le_mul_of_nonneg_left (show dist (vlast a) (xval a) ≤ δ / 4 by rw [dist_comm]; exact (hvprop a).2) hc
        have hs : s ≤ f (xval a) := (hxval a).1
        show t + ε ≤ f (vlast a)
        linarith [hb, hcd, hs, hεδ, hst2]
      let Φ : {S : Set X // S ∈ (fun x => {y | JoinedIn (superlevel f t) x y}) '' superlevel f s} →
          {T : Set ↥L // T ∈ (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ (t + ε) i j}) ''
            {i : ↥L | s - ε ≤ (fun x : ↥L => f x) i}} :=
        fun a => ⟨(fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ (t + ε) i j}) ⟨vlast a, (hvprop a).1⟩,
          ⟨⟨vlast a, (hvprop a).1⟩, by
            have hb := (abs_le.mp (hLip (vlast a) (xval a))).1
            have hcd : c * dist (vlast a) (xval a) ≤ c * (δ / 4) :=
              mul_le_mul_of_nonneg_left (show dist (vlast a) (xval a) ≤ δ / 4 by rw [dist_comm]; exact (hvprop a).2) hc
            have hs : s ≤ f (xval a) := (hxval a).1
            show s - ε ≤ f (vlast a)
            linarith [hb, hcd, hs, hεδ], rfl⟩⟩
      have hΦinj : Function.Injective Φ := by
        intro a₁ a₂ hEq
        have hsets : (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ (t + ε) i j}) ⟨vlast a₁, (hvprop a₁).1⟩ =
            (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ (t + ε) i j}) ⟨vlast a₂, (hvprop a₂).1⟩ :=
          congrArg Subtype.val hEq
        have hbr : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
            (t + ε) ⟨vlast a₂, (hvprop a₂).1⟩ ⟨vlast a₁, (hvprop a₁).1⟩ := by
          have hmem1 : (⟨vlast a₁, (hvprop a₁).1⟩ : ↥L) ∈
              (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
                (fun x : ↥L => f x) δ (t + ε) i j}) ⟨vlast a₁, (hvprop a₁).1⟩ :=
            ⟨hvhi a₁, Relation.ReflTransGen.refl⟩
          rw [hsets] at hmem1
          exact hmem1
        have hbr' : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
            (t + c * δ) ⟨vlast a₂, (hvprop a₂).1⟩ ⟨vlast a₁, (hvprop a₁).1⟩ := by
          rw [hεdef] at hbr; exact hbr
        have hj : JoinedIn (superlevel f t) (vlast a₂) (vlast a₁) :=
          T45Geo7.chain_super (Subtype.val : ↥L → X)
            (fun x y : ↥L => dist (x : X) (y : X))
            (fun a b => rfl) f c hc hLip δ t hδ hδρ
            ⟨vlast a₂, (hvprop a₂).1⟩ ⟨vlast a₁, (hvprop a₁).1⟩ hbr'
        have hlift : ∀ a, JoinedIn (superlevel f t) (xval a) (vlast a) := by
          intro a
          have hb := (abs_le.mp (hLip (vlast a) (xval a))).1
          have hcd := mul_le_mul_of_nonneg_left (show dist (vlast a) (xval a) ≤ δ / 4 by
            rw [dist_comm]; exact (hvprop a).2) hc
          have hcd2 : c * dist (xval a) (vlast a) ≤ c * (δ / 4) :=
            mul_le_mul_of_nonneg_left ((hvprop a).2) hc
          have hcd2' : c * dist (xval a) (vlast a) = c * dist (vlast a) (xval a) := by
            rw [dist_comm]
          have hs : s ≤ f (xval a) := (hxval a).1
          refine T45Geo7.lift f c hc hLip (xval a) (vlast a) t ?_ ?_ ?_
          · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith [(hvprop a).2, hδ])) hδρ
          · linarith [hcd2, hs, hεδ, hst2, hε0]
          · linarith [hb, hcd2', hcd, hs, hεδ, hst2, hε0]
        have hxx : JoinedIn (superlevel f t) (xval a₁) (xval a₂) :=
          JoinedIn.trans (JoinedIn.trans (hlift a₁) (JoinedIn.symm hj)) (JoinedIn.symm (hlift a₂))
        apply Subtype.ext
        rw [← (hxval a₁).2, ← (hxval a₂).2]
        ext z
        exact ⟨fun h => JoinedIn.trans (JoinedIn.symm hxx) h, fun h => JoinedIn.trans hxx h⟩
      have hcard := ENat.card_le_card_of_injective hΦinj
      simpa only [Set.encard] using hcard
    -- Direction 2: every Rips component of `L^t` meeting `L^s` lies in a path-component of
    -- `𝔽^{t+ε}` meeting `𝔽^{s-ε}`, injectively.
    have hdir2 : ripsRank (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ s t ≤
        superRank f (s - ε) (t + ε) := by
      classical
      show ((fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ t i j}) ''
             {i : ↥L | s ≤ (fun x : ↥L => f x) i}).encard ≤
           ((fun x => {y | JoinedIn (superlevel f (t + ε)) x y}) '' superlevel f (s - ε)).encard
      have hchoose : ∀ b : {S : Set ↥L // S ∈ (fun i => {j | ripsJoined
              (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ t i j}) ''
              {i : ↥L | s ≤ (fun x : ↥L => f x) i}},
          ∃ i : ↥L, s ≤ (fun x : ↥L => f x) i ∧
            (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ t i j}) i = (b : Set ↥L) :=
        fun b => b.2
      choose iv hiv using hchoose
      have hifilt : ∀ b, (iv b : X) ∈ superlevel f (s - ε) := by
        intro b
        show s - ε ≤ f (iv b : X)
        linarith [(hiv b).1, hε0]
      have hsamp : ∀ z : X, t + ε ≤ f z → ∃ v : ↥L, dist z (v : X) ≤ δ / 4 := by
        intro z hz
        have hzα : z ∈ superlevel f α := h1.antitone (by linarith [hat, hε0]) hz
        obtain ⟨v, hvL, hvd⟩ := hL z hzα
        exact ⟨⟨v, hvL⟩, hvd⟩
      let Ψ : {S : Set ↥L // S ∈ (fun i => {j | ripsJoined
              (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ t i j}) ''
              {i : ↥L | s ≤ (fun x : ↥L => f x) i}} →
          {T : Set X // T ∈ (fun x => {y | JoinedIn (superlevel f (t + ε)) x y}) '' superlevel f (s - ε)} :=
        fun b => ⟨(fun x => {y | JoinedIn (superlevel f (t + ε)) x y}) (iv b : X),
          ⟨(iv b : X), hifilt b, rfl⟩⟩
      have hΨinj : Function.Injective Ψ := by
        intro b₁ b₂ hEq
        have hsets : (fun x => {y | JoinedIn (superlevel f (t + ε)) x y}) (iv b₁ : X) =
                     (fun x => {y | JoinedIn (superlevel f (t + ε)) x y}) (iv b₂ : X) :=
          congrArg Subtype.val hEq
        have hjoined : JoinedIn (superlevel f (t + ε)) (iv b₁ : X) (iv b₂ : X) := by
          have hmem : (iv b₁ : X) ∈
              (fun x => {y | JoinedIn (superlevel f (t + ε)) x y}) (iv b₁ : X) :=
            JoinedIn.refl (by show t + ε ≤ f (iv b₁ : X); linarith [(hiv b₁).1, hst2, hε0])
          rw [hsets] at hmem
          exact JoinedIn.symm hmem
        have hrips := T45Geo7.chain_rips (Subtype.val : ↥L → X)
          (fun x y : ↥L => dist (x : X) (y : X)) (fun a b => rfl)
          (fun x : ↥L => f x) f (fun i => rfl) c hc hLip δ hδ (t + ε) hsamp (iv b₁) (iv b₂) hjoined
        have hrips' : ripsJoined (fun x y : ↥L => dist (x : X) (y : X)) (fun x : ↥L => f x) δ
            t (iv b₁) (iv b₂) :=
          h2.compat (by linarith [hεδ]) hrips
        have hR : (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ t i j}) (iv b₁) =
            (fun i => {j | ripsJoined (fun x y : ↥L => dist (x : X) (y : X))
              (fun x : ↥L => f x) δ t i j}) (iv b₂) := by
          ext j
          exact ⟨fun hj => h2.trans (h2.symm hrips') hj, fun hj => h2.trans hrips' hj⟩
        apply Subtype.ext
        rw [← (hiv b₁).2, ← (hiv b₂).2]
        exact hR
      have hcard := ENat.card_le_card_of_injective hΨinj
      simpa only [Set.encard] using hcard
    exact ⟨hdir1, hdir2⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
