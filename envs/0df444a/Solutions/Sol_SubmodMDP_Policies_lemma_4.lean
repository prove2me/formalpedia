-- Prove2me | solution 1 for SubmodMDP.Policies.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:38:35.820864+00:00
-- url     : https://prove2.me/submissions/5316d2a1-db8c-4d52-85f7-bd52bb819413

import Definitions.Def_SubmodMDP_Policies_Layered
import Theorems.Thm_SubmodMDP_Policies_lemma_3

open SubmodMDP.Policies

namespace Lemma4Aux

def IsBlockPath (G : LGraph) (off len : ℕ) (P : List (Fin G.N)) : Prop :=
  P.length = len ∧
  (∀ (i : ℕ) (hi : i < P.length), G.layer P[i] = off + i + 1) ∧
  (∀ (i : ℕ) (hi : i + 1 < P.length), G.arc P[i] P[i + 1] = true)

lemma inQ_mono_r (G : LGraph) {r r' : ℕ} (hrr : r' ≤ r) {x : Finset (Fin G.N) → ℝ}
    (hx : InQ G r x) : InQ G r' x := by
  rcases hx with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, h4, ?_⟩
  · intro i hi1 hi2 u v hu hv harc I hI
    exact h1 i hi1 hi2 u v hu hv harc I (le_trans hI hrr)
  · intro i hi1 hi2 I hI
    exact h2 i hi1 hi2 I (le_trans hI hrr)
  · intro v I hI
    exact h3 v I (le_trans hI hrr)
  · intro I hI
    exact h5 I (by omega)

lemma layerDist_eq_some (G : LGraph) (r : ℕ) (x : Finset (Fin G.N) → ℝ) (hx : InQ G r x)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ G.H) :
    ∃ hprob : (∀ w, G.layer w = i → 0 ≤ x {w}) ∧
        ∑ w, (if G.layer w = i then ENNReal.ofReal (x {w}) else 0) = 1,
      layerDist G x i =
        some (PMF.ofFintype (fun w => if G.layer w = i then ENNReal.ofReal (x {w}) else 0) hprob.2) := by
  have hnonneg : ∀ w, G.layer w = i → 0 ≤ x {w} := by
    intro w _
    exact hx.2.2.2.2 {w} (by simp)
  have hsum : ∑ w : Fin G.N, (if G.layer w = i then ENNReal.ofReal (x {w}) else 0) = 1 := by
    rw [← Finset.sum_filter]
    have hnonneg' : ∀ w ∈ Finset.univ.filter (fun w : Fin G.N => G.layer w = i), 0 ≤ x {w} := by
      intro w hw
      exact hnonneg w (Finset.mem_filter.mp hw).2
    rw [← ENNReal.ofReal_sum_of_nonneg hnonneg']
    have hsum_real : ∑ w ∈ Finset.univ.filter (fun w : Fin G.N => G.layer w = i), x {w} = 1 := by
      have h2 := hx.2.1 i hi1 hi2 ∅ (by simp)
      simpa [hx.2.2.2.1] using h2
    simp [hsum_real]
  let hp : (∀ w, G.layer w = i → 0 ≤ x {w}) ∧
      ∑ w, (if G.layer w = i then ENNReal.ofReal (x {w}) else 0) = 1 := ⟨hnonneg, hsum⟩
  refine ⟨hp, ?_⟩
  unfold layerDist
  rw [dif_pos hp]

noncomputable def rrrStep (G : LGraph) (_blk : ℕ)
    (sub : ℕ → (Finset (Fin G.N) → ℝ) → PMF (Option (List (Fin G.N))))
    (x : Finset (Fin G.N) → ℝ) (off : ℕ) :
    Option (List (Fin G.N)) → PMF (Option (List (Fin G.N)))
  | none => PMF.pure none
  | some P =>
    match P.getLast? with
    | none => PMF.pure none
    | some u =>
      if x {u} = 0 then PMF.pure none
      else (sub off (SubmodMDP.Policies.cond x u)).bind (fun o =>
        match o with
        | none => PMF.pure none
        | some Pi => PMF.pure (some (P ++ Pi)))

lemma rrrTail_succ_eq_bind (G : LGraph) (blk : ℕ)
    (sub : ℕ → (Finset (Fin G.N) → ℝ) → PMF (Option (List (Fin G.N))))
    (x : Finset (Fin G.N) → ℝ) :
    ∀ (k off : ℕ) (acc : List (Fin G.N)),
      rrrTail G blk sub x (k + 1) off acc =
        (rrrTail G blk sub x k off acc).bind (rrrStep G blk sub x (off + k * blk))
  | 0, off, acc => by
    simp only [rrrTail, Nat.zero_mul, add_zero, PMF.pure_bind]
    rfl
  | k + 1, off, acc => by
    rw [rrrTail.eq_2, rrrTail.eq_2]
    cases acc.getLast? with
    | none => simp [rrrStep]
    | some u =>
      by_cases hxu : x {u} = 0
      · simp [hxu, rrrStep]
      · simp only [hxu, ↓reduceIte, PMF.bind_bind]
        congr 1
        funext o
        cases o with
        | none => simp [rrrStep]
        | some Pi =>
          dsimp only
          rw [rrrTail_succ_eq_bind G blk sub x k (off + blk) (acc ++ Pi)]
          have heq : off + blk + k * blk = off + (k + 1) * blk := by ring
          rw [heq]

lemma blockPath_append {G : LGraph} {off len₁ len₂ : ℕ} {P₁ P₂ : List (Fin G.N)}
    (h1 : IsBlockPath G off len₁ P₁) (h2 : IsBlockPath G (off + len₁) len₂ P₂)
    (hlen1 : 1 ≤ len₁) (hlen2 : 1 ≤ len₂)
    (harc : G.arc (P₁[len₁ - 1]'(by have := h1.1; omega))
      (P₂[0]'(by have := h2.1; omega)) = true) :
    IsBlockPath G off (len₁ + len₂) (P₁ ++ P₂) := by
  have hlenP1 := h1.1
  have hlenP2 := h2.1
  refine ⟨by simp [hlenP1, hlenP2], ?_, ?_⟩
  · intro i hi
    simp only [List.length_append, h1.1, h2.1] at hi
    by_cases hilt : i < len₁
    · have hilt' : i < P₁.length := by omega
      rw [List.getElem_append_left hilt']
      exact h1.2.1 i hilt'
    · have hige : P₁.length ≤ i := by omega
      have hi2 : i - P₁.length < P₂.length := by omega
      rw [List.getElem_append_right hige]
      have hlay2 := h2.2.1 (i - P₁.length) hi2
      omega
  · intro i hi
    simp only [List.length_append, h1.1, h2.1] at hi
    by_cases hilt : i + 1 < len₁
    · have hilt1 : i < P₁.length := by omega
      have hilt2 : i + 1 < P₁.length := by omega
      rw [List.getElem_append_left hilt1, List.getElem_append_left hilt2]
      exact h1.2.2 i hilt2
    · by_cases hieq : i + 1 = len₁
      · have hi_eq : i = len₁ - 1 := by omega
        subst hi_eq
        have hilt1 : len₁ - 1 < P₁.length := by omega
        have hige2 : P₁.length ≤ len₁ - 1 + 1 := by omega
        rw [List.getElem_append_left hilt1, List.getElem_append_right hige2]
        have hsub : len₁ - 1 + 1 - P₁.length = 0 := by omega
        simpa [hsub] using harc
      · have hige1 : P₁.length ≤ i := by omega
        have hige2 : P₁.length ≤ i + 1 := by omega
        rw [List.getElem_append_right hige1, List.getElem_append_right hige2]
        have hsub : i + 1 - P₁.length = (i - P₁.length) + 1 := by omega
        have hi2 : (i - P₁.length) + 1 < P₂.length := by omega
        simpa [hsub] using h2.2.2 (i - P₁.length) hi2

lemma blockPath_mem_layer {G : LGraph} {off len : ℕ} {P : List (Fin G.N)}
    (hP : IsBlockPath G off len P) {v : Fin G.N} (hv : v ∈ P) :
    off + 1 ≤ G.layer v ∧ G.layer v ≤ off + len := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hlay := hP.2.1 i hi
  have hlen := hP.1
  omega

lemma blockPath_last_iff_mem {G : LGraph} {off len : ℕ} {P : List (Fin G.N)}
    (hP : IsBlockPath G off len P) (hlen : 1 ≤ len) {w : Fin G.N}
    (hw : G.layer w = off + len) :
    P.getLast? = some w ↔ w ∈ P := by
  have hlenP := hP.1
  have hlt : P.length - 1 < P.length := by omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlt, Option.some.injEq]
  constructor
  · intro heq
    rw [← heq]
    exact List.getElem_mem hlt
  · intro hmem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    have hi_lay := hP.2.1 i hi
    have hi_eq : i = P.length - 1 := by omega
    subst hi_eq
    rfl

lemma toOuterMeasure_total_of_none_not_mem {α : Type} (μ : PMF (Option α))
    (hnone : none ∉ μ.support) :
    μ.toOuterMeasure {o | ∃ a, o = some a} = 1 := by
  rw [PMF.toOuterMeasure_apply]
  have hcongr : ∀ o : Option α,
      ({o : Option α | ∃ a, o = some a} : Set (Option α)).indicator μ o = μ o := by
    intro o
    cases o with
    | none =>
      have h0 : μ none = 0 := by simpa [PMF.mem_support_iff] using hnone
      simp [Set.indicator, h0]
    | some _ => simp [Set.indicator]
  simp_rw [hcongr]
  exact μ.tsum_coe

lemma tsum_finset_sum_ennreal {α β : Type} (s : Finset β) (f : α → β → ENNReal) :
    (∑' a, ∑ b ∈ s, f a b) = ∑ b ∈ s, ∑' a, f a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hbs ih =>
    simp_rw [Finset.sum_insert hbs]
    rw [ENNReal.tsum_add, ih]

lemma rrr_props (G : LGraph) (hG : G.WF) (d : ℕ) (hd : 2 ≤ d) :
    ∀ (h off : ℕ) (x : Finset (Fin G.N) → ℝ),
      off + d ^ h ≤ G.H → InQ G h x →
      none ∉ (rrr G d h off x).support ∧
      (∀ P : List (Fin G.N), some P ∈ (rrr G d h off x).support →
        IsBlockPath G off (d ^ h) P) ∧
      ∀ v : Fin G.N,
        (rrr G d h off x).toOuterMeasure {o | ∃ P, o = some P ∧ v ∈ P} =
          if off + 1 ≤ G.layer v ∧ G.layer v ≤ off + d ^ h then ENNReal.ofReal (x {v}) else 0
  | 0, off, x, hoff, hx => by
    rw [Nat.pow_zero] at hoff ⊢
    obtain ⟨hprob, hld⟩ := layerDist_eq_some G 0 x hx (off + 1) (by omega) hoff
    simp only [rrr, hld]
    refine ⟨?_, ?_, ?_⟩
    · simp
    · intro P hP
      simp only [PMF.mem_support_map_iff, Option.some.injEq] at hP
      rcases hP with ⟨w, hw, rfl⟩
      simp only [PMF.mem_support_iff, PMF.ofFintype_apply] at hw
      have hlay : G.layer w = off + 1 := by
        by_contra hne
        simp [hne] at hw
      refine ⟨by simp, ?_, by simp⟩
      intro i hi
      simp only [List.length_singleton] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using hlay
    · intro v
      rw [PMF.toOuterMeasure_map_apply]
      have hpre : ((fun w : Fin G.N => some [w]) ⁻¹' {o | ∃ P, o = some P ∧ v ∈ P}) = {v} := by
        ext w
        simp [eq_comm]
      rw [hpre, PMF.toOuterMeasure_apply_singleton, PMF.ofFintype_apply]
      have hiff : (G.layer v = off + 1) ↔ (off + 1 ≤ G.layer v ∧ G.layer v ≤ off + 1) := by omega
      by_cases hv : G.layer v = off + 1
      · rw [if_pos hv, if_pos (hiff.mp hv)]
      · rw [if_neg hv, if_neg (mt hiff.mpr hv)]
  | h + 1, off, x, hoff, hx => by
    set blk := d ^ h with hblk_def
    have hblk_pos : 1 ≤ blk := Nat.one_le_pow h d (by omega)
    have hdh1 : d ^ (h + 1) = d * blk := by rw [Nat.pow_succ, hblk_def, mul_comm]
    have hoff_d : off + d * blk ≤ G.H := by rwa [← hdh1]
    -- Define prefix law after m tail steps (0 ≤ m ≤ d - 1)
    let pref : ℕ → PMF (Option (List (Fin G.N))) := fun m =>
      (rrr G d h off x).bind (fun o =>
        match o with
        | none => PMF.pure none
        | some P₁ => rrrTail G blk (rrr G d h) x m (off + blk) P₁)
    have hpref_zero : pref 0 = rrr G d h off x := by
      dsimp [pref]
      have hfun : (fun o : Option (List (Fin G.N)) =>
          match o with
          | none => PMF.pure none
          | some P₁ => rrrTail G blk (rrr G d h) x 0 (off + blk) P₁) = PMF.pure := by
        funext o
        cases o <;> rfl
      rw [hfun, PMF.bind_pure]
    have hpref_succ : ∀ m, pref (m + 1) =
        (pref m).bind (rrrStep G blk (rrr G d h) x (off + (m + 1) * blk)) := by
      intro m
      dsimp [pref]
      rw [PMF.bind_bind]
      congr 1
      funext o
      cases o with
      | none => simp [rrrStep]
      | some P₁ =>
        dsimp only
        rw [rrrTail_succ_eq_bind]
        have heq : off + blk + m * blk = off + (m + 1) * blk := by ring
        rw [heq]
    -- Prove the invariant for `pref m` for all `m ≤ d - 1`
    have hpref_inv : ∀ m ≤ d - 1,
        none ∉ (pref m).support ∧
        (∀ P : List (Fin G.N), some P ∈ (pref m).support →
          IsBlockPath G off ((m + 1) * blk) P) ∧
        ∀ v : Fin G.N,
          (pref m).toOuterMeasure {o | ∃ P, o = some P ∧ v ∈ P} =
            if off + 1 ≤ G.layer v ∧ G.layer v ≤ off + (m + 1) * blk then
              ENNReal.ofReal (x {v}) else 0 := by
      intro m
      induction m with
      | zero =>
        intro _
        rw [hpref_zero, Nat.zero_add, one_mul]
        have hoff_blk : off + d ^ h ≤ G.H := by
          rw [← hblk_def]
          have : 1 * blk ≤ d * blk := Nat.mul_le_mul_right blk (by omega)
          omega
        exact rrr_props G hG d hd h off x hoff_blk (inQ_mono_r G (Nat.le_succ h) hx)
      | succ m ih =>
        intro hm1
        obtain ⟨ih_none, ih_path, ih_marg⟩ := ih (by omega)
        rw [hpref_succ m]
        set off_next := off + (m + 1) * blk with hoff_next_def
        have hm1_blk_pos : 1 ≤ (m + 1) * blk := Nat.mul_pos (by omega : 0 < m + 1) hblk_pos
        have hoff_next_pos : 1 ≤ off_next := by omega
        have hoff_next_le : off_next + blk ≤ G.H := by
          have : (m + 2) * blk ≤ d * blk := Nat.mul_le_mul_right blk (by omega)
          have h2 : off_next + blk = off + (m + 2) * blk := by rw [hoff_next_def]; ring
          omega
        -- Helper for every `some P` in `(pref m).support`
        have hP_good : ∀ (P : List (Fin G.N)), some P ∈ (pref m).support →
            ∃ u : Fin G.N, P.getLast? = some u ∧
              (∃ hPlt : (m + 1) * blk - 1 < P.length, u = P[(m + 1) * blk - 1]'hPlt) ∧
              G.layer u = off_next ∧ 0 < x {u} := by
          intro P hPsupp
          have hPblk := ih_path P hPsupp
          have hPlen := hPblk.1
          have hidx : P.length - 1 < P.length := by omega
          set u := P[P.length - 1]
          have hlast : P.getLast? = some u := by
            rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hidx]
          have hulay : G.layer u = off_next := by
            have := hPblk.2.1 (P.length - 1) hidx
            dsimp [u]
            omega
          have hu_mem : u ∈ P := List.getElem_mem hidx
          have hpos_meas : 0 < (pref m).toOuterMeasure {o | ∃ Q, o = some Q ∧ u ∈ Q} := by
            have hle : (pref m) (some P) ≤
                (pref m).toOuterMeasure {o | ∃ Q, o = some Q ∧ u ∈ Q} := by
              rw [← PMF.toOuterMeasure_apply_singleton]
              exact (pref m).toOuterMeasure.mono (by intro o ho; subst ho; exact ⟨P, rfl, hu_mem⟩)
            have hposP : 0 < (pref m) (some P) :=
              pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp hPsupp)
            exact lt_of_lt_of_le hposP hle
          rw [ih_marg u] at hpos_meas
          have hu_in_range : off + 1 ≤ G.layer u ∧ G.layer u ≤ off + (m + 1) * blk := by omega
          rw [if_pos hu_in_range, ENNReal.ofReal_pos] at hpos_meas
          refine ⟨u, hlast, ⟨by omega, ?_⟩, hulay, hpos_meas⟩
          simp [u, hPlen]
        refine ⟨?_, ?_, ?_⟩
        · -- Part 1: none ∉ support
          intro hnone
          rw [PMF.mem_support_bind_iff] at hnone
          rcases hnone with ⟨o, ho, hstep⟩
          cases o with
          | none => exact ih_none ho
          | some P =>
            obtain ⟨u, hlast, _, _, hxu_pos⟩ := hP_good P ho
            have hcond_inQ : InQ G h (SubmodMDP.Policies.cond x u) :=
              SubmodMDP.Policies.lemma_3 G (h + 1) (by omega) x hx u hxu_pos
            obtain ⟨sub_none, _, _⟩ :=
              rrr_props G hG d hd h off_next (SubmodMDP.Policies.cond x u) hoff_next_le hcond_inQ
            simp only [rrrStep, hlast, hxu_pos.ne', ↓reduceIte, PMF.mem_support_bind_iff] at hstep
            rcases hstep with ⟨o2, ho2, hstep2⟩
            cases o2 with
            | none => exact sub_none ho2
            | some Pi => simp at hstep2
        · -- Part 2: IsBlockPath
          intro Q hQ
          rw [PMF.mem_support_bind_iff] at hQ
          rcases hQ with ⟨o, ho, hstep⟩
          cases o with
          | none => exact (ih_none ho).elim
          | some P =>
            have hPblk := ih_path P ho
            obtain ⟨u, hlast, ⟨hPlt, hu_eq⟩, hulay, hxu_pos⟩ := hP_good P ho
            have hcond_inQ : InQ G h (SubmodMDP.Policies.cond x u) :=
              SubmodMDP.Policies.lemma_3 G (h + 1) (by omega) x hx u hxu_pos
            obtain ⟨sub_none, sub_path, sub_marg⟩ :=
              rrr_props G hG d hd h off_next (SubmodMDP.Policies.cond x u) hoff_next_le hcond_inQ
            simp only [rrrStep, hlast, hxu_pos.ne', ↓reduceIte, PMF.mem_support_bind_iff] at hstep
            rcases hstep with ⟨o2, ho2, hstep2⟩
            cases o2 with
            | none => exact (sub_none ho2).elim
            | some Pi =>
              simp only [PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at hstep2
              subst hstep2
              have hPiblk := sub_path Pi ho2
              have hPi0_lt : 0 < Pi.length := by
                have := hPiblk.1
                omega
              set v₀ := Pi[0]
              have hv0_lay : G.layer v₀ = off_next + 1 := by
                have := hPiblk.2.1 0 hPi0_lt
                omega
              have hv0_mem : v₀ ∈ Pi := List.getElem_mem hPi0_lt
              have hv0_meas_pos : 0 < (rrr G d h off_next (SubmodMDP.Policies.cond x u)).toOuterMeasure
                  {o | ∃ R, o = some R ∧ v₀ ∈ R} := by
                have hle : (rrr G d h off_next (SubmodMDP.Policies.cond x u)) (some Pi) ≤
                    (rrr G d h off_next (SubmodMDP.Policies.cond x u)).toOuterMeasure
                      {o | ∃ R, o = some R ∧ v₀ ∈ R} := by
                  rw [← PMF.toOuterMeasure_apply_singleton]
                  exact (rrr G d h off_next (SubmodMDP.Policies.cond x u)).toOuterMeasure.mono
                    (by intro o ho'; subst ho'; exact ⟨Pi, rfl, hv0_mem⟩)
                have hposPi := pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp ho2)
                exact lt_of_lt_of_le hposPi hle
              rw [sub_marg v₀] at hv0_meas_pos
              have hv0_range : off_next + 1 ≤ G.layer v₀ ∧ G.layer v₀ ≤ off_next + blk := by omega
              rw [if_pos hv0_range, ENNReal.ofReal_pos] at hv0_meas_pos
              dsimp only [SubmodMDP.Policies.cond] at hv0_meas_pos
              have hxuv_pos : 0 < x (insert u {v₀}) := by
                by_contra hnp
                have hdiv : x (insert u {v₀}) / x {u} ≤ 0 :=
                  div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnp) hxu_pos.le
                linarith
              have harc_uv : G.arc u v₀ = true := by
                by_contra hnoarc
                have hfalse : G.arc u v₀ = false := Bool.eq_false_iff.mpr hnoarc
                have hoff_next_lt_H : off_next ≤ G.H - 1 := by omega
                have h1 := hx.1 off_next hoff_next_pos hoff_next_lt_H
                  u v₀ hulay hv0_lay hfalse {u} (by simp)
                have hins' : insert v₀ ({u} : Finset (Fin G.N)) = insert u {v₀} :=
                  Finset.pair_comm v₀ u
                have hself : insert u ({u} : Finset (Fin G.N)) = {u} := by simp
                rw [hself, hins'] at h1
                linarith
              have harc' : G.arc (P[(m + 1) * blk - 1]'hPlt) (Pi[0]'hPi0_lt) = true := by
                rwa [← hu_eq]
              have hcat := blockPath_append hPblk hPiblk hm1_blk_pos hblk_pos harc'
              have hlen_eq : (m + 1) * blk + blk = (m + 1 + 1) * blk := by ring
              rwa [hlen_eq] at hcat
        · -- Part 3: Marginals
          intro v
          rw [PMF.toOuterMeasure_bind_apply]
          -- Helper evaluating the conditional probability for each `o`
          by_cases hv_prev : off + 1 ≤ G.layer v ∧ G.layer v ≤ off_next
          · -- Case A: v is in the first (m+1)*blk layers
            have hv_all : off + 1 ≤ G.layer v ∧ G.layer v ≤ off + (m + 1 + 1) * blk := by
              refine ⟨hv_prev.1, ?_⟩
              have : off_next ≤ off + (m + 1 + 1) * blk := by dsimp [off_next]; nlinarith
              omega
            simp only [hv_all, and_self, ↓reduceIte]
            have hterm : ∀ o : Option (List (Fin G.N)),
                (pref m) o * (rrrStep G blk (rrr G d h) x off_next o).toOuterMeasure
                  {o' | ∃ Q, o' = some Q ∧ v ∈ Q} =
                (pref m) o * ({o' | ∃ P, o' = some P ∧ v ∈ P} : Set _).indicator 1 o := by
              intro o
              by_cases ho : o ∈ (pref m).support
              · cases o with
                | none => exact (ih_none ho).elim
                | some P =>
                  obtain ⟨u, hlast, _, _, hxu_pos⟩ := hP_good P ho
                  have hcond_inQ : InQ G h (SubmodMDP.Policies.cond x u) :=
                    SubmodMDP.Policies.lemma_3 G (h + 1) (by omega) x hx u hxu_pos
                  obtain ⟨sub_none, sub_path, _⟩ := rrr_props G hG d hd h off_next
                    (SubmodMDP.Policies.cond x u) hoff_next_le hcond_inQ
                  congr 1
                  simp only [rrrStep, hlast, hxu_pos.ne', ↓reduceIte]
                  rw [PMF.toOuterMeasure_bind_apply]
                  by_cases hvP : v ∈ P
                  · have hind : ({o' : Option (List (Fin G.N)) | ∃ P', o' = some P' ∧ v ∈ P'}).indicator
                        (1 : Option (List (Fin G.N)) → ENNReal) (some P) = 1 := by
                      simp [Set.indicator, hvP]
                    rw [hind]
                    have hsub1 : ∀ o2 : Option (List (Fin G.N)),
                        (rrr G d h off_next (SubmodMDP.Policies.cond x u)) o2 *
                          (match o2 with
                          | none => PMF.pure none
                          | some Pi => PMF.pure (some (P ++ Pi))).toOuterMeasure
                            {o' | ∃ Q, o' = some Q ∧ v ∈ Q} =
                        ({o' | ∃ Pi, o' = some Pi} : Set _).indicator
                          (rrr G d h off_next (SubmodMDP.Policies.cond x u)) o2 := by
                      intro o2
                      cases o2 with
                      | none => simp [Set.indicator]
                      | some Pi =>
                        simp [PMF.toOuterMeasure_pure_apply, Set.indicator, hvP]
                    simp_rw [hsub1, ← PMF.toOuterMeasure_apply]
                    exact toOuterMeasure_total_of_none_not_mem _ sub_none
                  · have hind : ({o' : Option (List (Fin G.N)) | ∃ P', o' = some P' ∧ v ∈ P'}).indicator
                        (1 : Option (List (Fin G.N)) → ENNReal) (some P) = 0 := by
                      simp [Set.indicator, hvP]
                    rw [hind]
                    refine ENNReal.tsum_eq_zero.mpr fun o2 => ?_
                    by_cases ho2 : o2 ∈ (rrr G d h off_next (SubmodMDP.Policies.cond x u)).support
                    · cases o2 with
                      | none => exact (sub_none ho2).elim
                      | some Pi =>
                        have hPiblk := sub_path Pi ho2
                        have hvPi : v ∉ Pi := by
                          intro hmem
                          have hlay := blockPath_mem_layer hPiblk hmem
                          omega
                        simp [PMF.toOuterMeasure_pure_apply, hvP, hvPi]
                    · simp only [PMF.mem_support_iff, not_not] at ho2
                      simp [ho2]
              · simp only [PMF.mem_support_iff, not_not] at ho
                simp [ho]
            simp_rw [hterm]
            have hmul_ind : ∀ o : Option (List (Fin G.N)),
                (pref m) o * ({o' | ∃ P, o' = some P ∧ v ∈ P} : Set _).indicator 1 o =
                ({o' | ∃ P, o' = some P ∧ v ∈ P} : Set _).indicator (pref m) o := by
              intro o
              by_cases hm_in : o ∈ ({o' : Option (List (Fin G.N)) | ∃ P, o' = some P ∧ v ∈ P})
              · simp [Set.indicator, hm_in]
              · simp [Set.indicator, hm_in]
            simp_rw [hmul_ind, ← PMF.toOuterMeasure_apply]
            rw [ih_marg v, if_pos hv_prev]
          · by_cases hv_new : off_next + 1 ≤ G.layer v ∧ G.layer v ≤ off_next + blk
            · -- Case B: v is in the new block (off_next + 1 .. off_next + blk)
              have hv_all : off + 1 ≤ G.layer v ∧ G.layer v ≤ off + (m + 1 + 1) * blk := by
                refine ⟨by omega, ?_⟩
                have : off_next + blk = off + (m + 1 + 1) * blk := by dsimp [off_next]; ring
                omega
              simp only [hv_all, and_self, ↓reduceIte]
              -- Express each o's contribution as a finite sum over w ∈ layer off_next
              let S_lay := Finset.univ.filter (fun w : Fin G.N => G.layer w = off_next)
              have hterm : ∀ o : Option (List (Fin G.N)),
                  (pref m) o * (rrrStep G blk (rrr G d h) x off_next o).toOuterMeasure
                    {o' | ∃ Q, o' = some Q ∧ v ∈ Q} =
                  ∑ w ∈ S_lay,
                    ({o' | ∃ P, o' = some P ∧ w ∈ P} : Set _).indicator (pref m) o *
                      ENNReal.ofReal (SubmodMDP.Policies.cond x w {v}) := by
                intro o
                by_cases ho : o ∈ (pref m).support
                · cases o with
                  | none => exact (ih_none ho).elim
                  | some P =>
                    have hPblk := ih_path P ho
                    obtain ⟨u, hlast, _, hulay, hxu_pos⟩ := hP_good P ho
                    have hcond_inQ : InQ G h (SubmodMDP.Policies.cond x u) :=
                      SubmodMDP.Policies.lemma_3 G (h + 1) (by omega) x hx u hxu_pos
                    obtain ⟨sub_none, _, sub_marg⟩ := rrr_props G hG d hd h off_next
                      (SubmodMDP.Policies.cond x u) hoff_next_le hcond_inQ
                    have hvP : v ∉ P := by
                      intro hmem
                      have hlay := blockPath_mem_layer hPblk hmem
                      exact hv_prev hlay
                    have hlhs : (rrrStep G blk (rrr G d h) x off_next (some P)).toOuterMeasure
                        {o' | ∃ Q, o' = some Q ∧ v ∈ Q} =
                        ENNReal.ofReal (SubmodMDP.Policies.cond x u {v}) := by
                      simp only [rrrStep, hlast, hxu_pos.ne', ↓reduceIte]
                      rw [PMF.toOuterMeasure_bind_apply]
                      have hsub_eq : ∀ o2 : Option (List (Fin G.N)),
                          (rrr G d h off_next (SubmodMDP.Policies.cond x u)) o2 *
                            (match o2 with
                            | none => PMF.pure none
                            | some Pi => PMF.pure (some (P ++ Pi))).toOuterMeasure
                              {o' | ∃ Q, o' = some Q ∧ v ∈ Q} =
                          ({o' | ∃ Pi, o' = some Pi ∧ v ∈ Pi} : Set _).indicator
                            (rrr G d h off_next (SubmodMDP.Policies.cond x u)) o2 := by
                        intro o2
                        cases o2 with
                        | none => simp [Set.indicator]
                        | some Pi =>
                          by_cases hvPi : v ∈ Pi
                          · simp [PMF.toOuterMeasure_pure_apply, Set.indicator, hvPi]
                          · simp [PMF.toOuterMeasure_pure_apply, Set.indicator, hvP, hvPi]
                      simp_rw [hsub_eq, ← PMF.toOuterMeasure_apply]
                      rw [sub_marg v, if_pos hv_new]
                    rw [hlhs]
                    have hu_mem_S : u ∈ S_lay := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hulay⟩
                    have hlen1_pos : 1 ≤ (m + 1) * blk := Nat.mul_pos (by omega) hblk_pos
                    rw [Finset.sum_eq_single u]
                    · have huP : u ∈ P :=
                        (blockPath_last_iff_mem hPblk hlen1_pos hulay).mp hlast
                      simp [Set.indicator, huP]
                    · intro w hw hwu
                      have hwlay : G.layer w = off_next := (Finset.mem_filter.mp hw).2
                      have hw_not_P : w ∉ P := by
                        intro hwP
                        have hw_last := (blockPath_last_iff_mem hPblk hlen1_pos hwlay).mpr hwP
                        rw [hlast, Option.some.injEq] at hw_last
                        exact hwu hw_last.symm
                      simp [Set.indicator, hw_not_P]
                    · intro hnot
                      exact (hnot hu_mem_S).elim
                · simp only [PMF.mem_support_iff, not_not] at ho
                  have hrhs0 : ∑ w ∈ S_lay,
                      ({o' | ∃ P, o' = some P ∧ w ∈ P} : Set _).indicator (pref m) o *
                        ENNReal.ofReal (SubmodMDP.Policies.cond x w {v}) = 0 := by
                    refine Finset.sum_eq_zero fun w _ => ?_
                    by_cases hm_in : o ∈ ({o' : Option (List (Fin G.N)) | ∃ P, o' = some P ∧ w ∈ P})
                    · simp [Set.indicator, hm_in, ho]
                    · simp [Set.indicator, hm_in]
                  simp [ho, hrhs0]
              simp_rw [hterm]
              rw [tsum_finset_sum_ennreal]
              have hsum_w : ∀ w ∈ S_lay,
                  (∑' o, ({o' | ∃ P, o' = some P ∧ w ∈ P} : Set _).indicator (pref m) o *
                    ENNReal.ofReal (SubmodMDP.Policies.cond x w {v})) =
                  ENNReal.ofReal (x (insert w {v})) := by
                intro w hw
                rw [ENNReal.tsum_mul_right, ← PMF.toOuterMeasure_apply, ih_marg w]
                have hwlay : G.layer w = off_next := (Finset.mem_filter.mp hw).2
                have hw_range : off + 1 ≤ G.layer w ∧ G.layer w ≤ off + (m + 1) * blk := by omega
                rw [if_pos hw_range]
                dsimp only [SubmodMDP.Policies.cond]
                have hxw_nn : 0 ≤ x {w} := hx.2.2.2.2 {w} (by simp)
                have hxiv_nn : 0 ≤ x (insert w {v}) := by
                  refine hx.2.2.2.2 (insert w {v}) ?_
                  have := Finset.card_insert_le w {v}
                  simp at this
                  omega
                rw [← ENNReal.ofReal_mul hxw_nn]
                by_cases hxw0 : x {w} = 0
                · have hle : x (insert w {v}) ≤ x {w} := by
                    rw [Finset.pair_comm w v]
                    exact hx.2.2.1 v {w} (by simp)
                  have heq0 : x (insert w {v}) = 0 := le_antisymm (by linarith) hxiv_nn
                  simp [hxw0, heq0]
                · rw [mul_div_cancel₀ _ hxw0]
              rw [Finset.sum_congr rfl hsum_w]
              rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => by
                refine hx.2.2.2.2 (insert w {v}) ?_
                have := Finset.card_insert_le w {v}
                simp at this
                omega)]
              have hsum_inQ := hx.2.1 off_next hoff_next_pos (by omega) {v}
                (by simp)
              dsimp [S_lay]
              rw [hsum_inQ]
            · -- Case C: v is outside [off + 1, off + (m + 2) * blk]
              have hv_not_all : ¬ (off + 1 ≤ G.layer v ∧ G.layer v ≤ off + (m + 1 + 1) * blk) := by
                have heq : off_next + blk = off + (m + 1 + 1) * blk := by dsimp [off_next]; ring
                omega
              simp only [hv_not_all, ↓reduceIte]
              refine ENNReal.tsum_eq_zero.mpr fun o => ?_
              by_cases ho : o ∈ (pref m).support
              · cases o with
                | none => exact (ih_none ho).elim
                | some P =>
                  have hPblk := ih_path P ho
                  obtain ⟨u, hlast, _, _, hxu_pos⟩ := hP_good P ho
                  have hcond_inQ : InQ G h (SubmodMDP.Policies.cond x u) :=
                    SubmodMDP.Policies.lemma_3 G (h + 1) (by omega) x hx u hxu_pos
                  obtain ⟨sub_none, sub_path, _⟩ := rrr_props G hG d hd h off_next
                    (SubmodMDP.Policies.cond x u) hoff_next_le hcond_inQ
                  have hvP : v ∉ P := fun hm => hv_prev (blockPath_mem_layer hPblk hm)
                  simp only [rrrStep, hlast, hxu_pos.ne', ↓reduceIte, mul_eq_zero]
                  right
                  rw [PMF.toOuterMeasure_bind_apply]
                  refine ENNReal.tsum_eq_zero.mpr fun o2 => ?_
                  by_cases ho2 : o2 ∈ (rrr G d h off_next (SubmodMDP.Policies.cond x u)).support
                  · cases o2 with
                    | none => exact (sub_none ho2).elim
                    | some Pi =>
                      have hvPi : v ∉ Pi :=
                        fun hm => hv_new (blockPath_mem_layer (sub_path Pi ho2) hm)
                      simp [PMF.toOuterMeasure_pure_apply, hvP, hvPi]
                  · simp only [PMF.mem_support_iff, not_not] at ho2
                    simp [ho2]
              · simp only [PMF.mem_support_iff, not_not] at ho
                simp [ho]
    -- Apply hpref_inv at m = d - 1
    have hfinal := hpref_inv (d - 1) (le_refl _)
    have hdm1 : (d - 1 + 1) * blk = d ^ (h + 1) := by
      have : d - 1 + 1 = d := by omega
      rw [this, hdh1]
    rw [hdm1] at hfinal
    exact hfinal

end Lemma4Aux

theorem solution (G : LGraph) (hG : G.WF) (d r : ℕ) (hd : 2 ≤ d) (hH : G.H = d ^ r)
    (x : Finset (Fin G.N) → ℝ) (hx : InQ G r x) :
    none ∉ (RRR G d r x).support ∧
    (∀ P : List (Fin G.N), some P ∈ (RRR G d r x).support → IsLSPath G P) ∧
    ∀ v : Fin G.N,
      (RRR G d r x).toOuterMeasure {o | ∃ P, o = some P ∧ v ∈ P} = ENNReal.ofReal (x {v}) := by
  obtain ⟨h1, h2, h3⟩ := Lemma4Aux.rrr_props G hG d hd r 0 x (by omega) hx
  refine ⟨h1, ?_, ?_⟩
  · intro P hP
    obtain ⟨hlen, hlay, harc⟩ := h2 P hP
    exact ⟨by omega, fun i hi => by simpa using hlay i hi, harc⟩
  · intro v
    rw [RRR, h3 v]
    have hvlay := hG.1 v
    have hrange : 0 + 1 ≤ G.layer v ∧ G.layer v ≤ 0 + d ^ r := by omega
    rw [if_pos hrange]
