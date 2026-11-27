-- Prove2me | solution 1 for PrivPCP.Bonus.lemma_4_8_noproper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:03:41.589896+00:00
-- url     : https://prove2.me/submissions/d521248a-1eed-409b-80a0-1d7d17e74103

import Mathlib
import Definitions.Def_PrivPCP_IsCollectivelyPE


namespace PrivPCP.Lemma48Aux

open Classical GoodQLTC

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

/-- the `I`-flat through `ω`: points agreeing with `ω` outside `I` -/
noncomputable def flat (I : Finset ι) (ω : ∀ i, S i) : Finset (∀ i, S i) :=
  Finset.univ.filter fun ω' => ∀ j, j ∉ I → ω' j = ω j

lemma mem_flat {I : Finset ι} {ω ω' : ∀ i, S i} : ω' ∈ flat I ω ↔ ∀ j, j ∉ I → ω' j = ω j := by
  simp [flat]

lemma self_mem_flat (I : Finset ι) (ω : ∀ i, S i) : ω ∈ flat I ω := mem_flat.2 fun _ _ => rfl

lemma flat_eq_of_mem {I : Finset ι} {ω ω' : ∀ i, S i} (h : ω' ∈ flat I ω) :
    flat I ω' = flat I ω := by
  rw [mem_flat] at h
  ext x
  simp only [mem_flat]
  constructor
  · intro hx j hj; rw [hx j hj, h j hj]
  · intro hx j hj; rw [hx j hj, h j hj]

lemma flat_mono {I J : Finset ι} (h : I ⊆ J) (ω : ∀ i, S i) : flat I ω ⊆ flat J ω := by
  intro x hx
  rw [mem_flat] at hx ⊢
  exact fun j hj => hx j (fun hI => hj (h hI))

lemma flat_eq_piFinset (I : Finset ι) (ω : ∀ i, S i) :
    flat I ω = Fintype.piFinset (fun i => if i ∈ I then Finset.univ else {ω i}) := by
  ext x
  simp only [mem_flat, Fintype.mem_piFinset]
  constructor
  · intro h i
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi, h i hi]
  · intro h j hj
    have := h j
    simpa [hj] using this

lemma card_flat (I : Finset ι) (ω : ∀ i, S i) :
    (flat I ω).card = ∏ i ∈ I, Fintype.card (S i) := by
  rw [flat_eq_piFinset, Fintype.card_piFinset]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ I)]
  have h1 : ∏ x ∈ Finset.univ.filter (fun i => i ∈ I),
      (if x ∈ I then (Finset.univ : Finset (S x)) else {ω x}).card =
      ∏ i ∈ I, Fintype.card (S i) := by
    rw [Finset.filter_univ_mem]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [hi]
  have h2 : ∏ x ∈ Finset.univ.filter (fun i => ¬ i ∈ I),
      (if x ∈ I then (Finset.univ : Finset (S x)) else {ω x}).card = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  rw [h1, h2, mul_one]

lemma update_mem_flat (ω : ∀ i, S i) (i : ι) (t : S i) :
    Function.update ω i t ∈ flat {i} ω := by
  rw [mem_flat]
  intro j hj
  rw [Finset.mem_singleton] at hj
  rw [Function.update_of_ne hj]

/-- projection forgetting coordinate `i` (the line index used by `lineCount`) -/
def proj (i : ι) (ω : ∀ i, S i) : (j : {j // j ≠ i}) → S j.1 := fun j => ω j.1

lemma proj_eq_iff (i : ι) (ω ω' : ∀ i, S i) : proj i ω' = proj i ω ↔ ω' ∈ flat {i} ω := by
  rw [mem_flat]
  constructor
  · intro h j hj
    rw [Finset.mem_singleton] at hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j.1 (by simpa using j.2)

/-- the fiber of the line index `β` -/
noncomputable def fiber (i : ι) (β : (j : {j // j ≠ i}) → S j.1) : Finset (∀ i, S i) :=
  Finset.univ.filter fun ω => proj i ω = β

lemma fiber_proj (i : ι) (ω : ∀ i, S i) : fiber i (proj i ω) = flat {i} ω := by
  ext x
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact proj_eq_iff i ω x

end PrivPCP.Lemma48Aux


namespace PrivPCP.Lemma48Aux

open Classical GoodQLTC

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

/-- `ρ`-closed sets -/
def IsClosedSet (ρ : ℝ) (B : Finset (∀ i, S i)) : Prop :=
  ∀ i ω, ¬ flat {i} ω ⊆ B → ((B ∩ flat {i} ω).card : ℝ) < ρ * Fintype.card (S i)

/-- heavy flats -/
def heavy (ε : ℝ) (A : Finset (∀ i, S i)) (I : Finset ι) (ω : ∀ i, S i) : Prop :=
  (∏ i ∈ I, ε * (Fintype.card (S i) : ℝ)) ≤ ((A ∩ flat I ω).card : ℝ)

lemma heavy_congr {ε : ℝ} {A : Finset (∀ i, S i)} {I : Finset ι} {ω ω' : ∀ i, S i}
    (h : ω' ∈ flat I ω) : heavy ε A I ω' ↔ heavy ε A I ω := by
  rw [heavy, heavy, flat_eq_of_mem h]

noncomputable def closureSet (ε : ℝ) (A : Finset (∀ i, S i)) : Finset (∀ i, S i) :=
  Finset.univ.filter fun ω => ∃ I, heavy ε A I ω

lemma subset_closureSet (ε : ℝ) (A : Finset (∀ i, S i)) : A ⊆ closureSet ε A := by
  intro ω hω
  simp only [closureSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨∅, ?_⟩
  simp only [heavy, Finset.prod_empty, Nat.one_le_cast]
  exact Finset.card_pos.mpr ⟨ω, Finset.mem_inter.mpr ⟨hω, self_mem_flat _ _⟩⟩

lemma card_inter_flat_sum (A : Finset (∀ i, S i)) (I : Finset ι) :
    ∑ ω, (A ∩ flat I ω).card = A.card * ∏ i ∈ I, Fintype.card (S i) := by
  have hsymm : ∀ a ω : ∀ i, S i, a ∈ flat I ω ↔ ω ∈ flat I a := by
    intro a ω; simp only [mem_flat]
    exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  have : ∀ ω, (A ∩ flat I ω).card = ∑ a ∈ A, if ω ∈ flat I a then 1 else 0 := by
    intro ω
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hsymm]
  simp_rw [this]
  rw [Finset.sum_comm]
  have h2 : ∀ a, (∑ ω : (∀ i, S i), if ω ∈ flat I a then 1 else 0) = (flat I a).card := by
    intro a
    rw [← Finset.card_filter]
    congr 1
    ext x; simp
  simp_rw [h2, card_flat, Finset.sum_const, smul_eq_mul]

lemma closureSet_closed {ρ : ℝ} (hρ : 0 < ρ) (A : Finset (∀ i, S i)) :
    IsClosedSet ρ (closureSet (ρ / 2 ^ Fintype.card ι) A) := by
  set ε := ρ / 2 ^ Fintype.card ι with hε
  have hεpos : 0 < ε := by positivity
  intro i ω hnot
  have hspos : (0 : ℝ) < Fintype.card (S i) := by
    have : Nonempty (S i) := ⟨ω i⟩
    exact_mod_cast Fintype.card_pos
  set B := closureSet ε A
  -- each term
  have hterm : ∀ I : Finset ι,
      (((Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω).card : ℝ) <
        ε * Fintype.card (S i) := by
    intro I
    set T := (Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω with hT
    by_cases hiI : i ∈ I
    · have hT0 : T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [hT, Finset.mem_inter, Finset.mem_filter] at hx
        obtain ⟨⟨-, hhx⟩, hxf⟩ := hx
        apply hnot
        intro y hy
        have hxI : x ∈ flat I ω := flat_mono (by simpa using hiI) ω hxf
        have hyI : y ∈ flat I ω := flat_mono (by simpa using hiI) ω hy
        have : heavy ε A I y := by
          rw [heavy_congr hyI]; rw [heavy_congr hxI] at hhx; exact hhx
        simp only [B, closureSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨I, this⟩
      rw [hT0, Finset.card_empty, Nat.cast_zero]
      positivity
    · by_contra hge
      push Not at hge
      apply hnot
      set J := insert i I
      have hheavy : heavy ε A J ω := by
        unfold heavy
        rw [Finset.prod_insert hiI]
        have hprod_nonneg : 0 ≤ ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ) :=
          Finset.prod_nonneg fun _ _ => by positivity
        calc ε * (Fintype.card (S i) : ℝ) * ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ)
            ≤ (T.card : ℝ) * ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ) :=
              mul_le_mul_of_nonneg_right hge hprod_nonneg
          _ ≤ ∑ x ∈ T, ((A ∩ flat I x).card : ℝ) := by
              rw [← nsmul_eq_mul]
              rw [← Finset.sum_const]
              refine Finset.sum_le_sum fun x hx => ?_
              rw [hT, Finset.mem_inter, Finset.mem_filter] at hx
              exact hx.1.2
          _ = ((T.biUnion fun x => A ∩ flat I x).card : ℝ) := by
              rw [Finset.card_biUnion]
              · push_cast; rfl
              · intro x hx x' hx' hne
                rw [Function.onFun, Finset.disjoint_left]
                intro y hy hy'
                apply hne
                rw [Finset.mem_coe, hT, Finset.mem_inter] at hx hx'
                have h1 := mem_flat.1 (Finset.mem_inter.1 hy).2 i hiI
                have h2 := mem_flat.1 (Finset.mem_inter.1 hy').2 i hiI
                funext j
                by_cases hj : j = i
                · subst hj; rw [← h1, ← h2]
                · have := mem_flat.1 hx.2 j (by simpa using hj)
                  have h' := mem_flat.1 hx'.2 j (by simpa using hj)
                  rw [this, h']
          _ ≤ ((A ∩ flat J ω).card : ℝ) := by
              norm_cast
              apply Finset.card_le_card
              intro y hy
              rw [Finset.mem_biUnion] at hy
              obtain ⟨x, hx, hy⟩ := hy
              rw [hT, Finset.mem_inter] at hx
              rw [Finset.mem_inter] at hy ⊢
              refine ⟨hy.1, ?_⟩
              rw [mem_flat]
              intro j hj
              have hji : j ≠ i := fun h => hj (by simp [J, h])
              have hjI : j ∉ I := fun h => hj (by simp [J, h])
              rw [mem_flat.1 hy.2 j hjI, mem_flat.1 hx.2 j (by simpa using hji)]
      intro y hy
      have hyJ : y ∈ flat J ω := flat_mono (by simp [J]) ω hy
      simp only [B, closureSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨J, (heavy_congr hyJ).2 hheavy⟩
  -- sum up
  have hBsub : B ∩ flat {i} ω ⊆
      (Finset.univ : Finset (Finset ι)).biUnion
        fun I => (Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω := by
    intro x hx
    rw [Finset.mem_inter] at hx
    simp only [B, closureSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨I, hI⟩, hxf⟩ := hx
    rw [Finset.mem_biUnion]
    exact ⟨I, Finset.mem_univ _, Finset.mem_inter.2 ⟨by simpa using hI, hxf⟩⟩
  calc ((B ∩ flat {i} ω).card : ℝ)
      ≤ (((Finset.univ : Finset (Finset ι)).biUnion
        fun I => (Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hBsub
    _ ≤ ∑ I : Finset ι, (((Finset.univ.filter fun x => heavy ε A I x) ∩ flat {i} ω).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ < ∑ _I : Finset ι, ε * (Fintype.card (S i) : ℝ) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun I _ => hterm I
    _ = ρ * Fintype.card (S i) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, hε]
        push_cast
        field_simp

lemma closureSet_card {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (A : Finset (∀ i, S i)) :
    ((closureSet (ρ / 2 ^ Fintype.card ι) A).card : ℝ) ≤
      ((2 ^ Fintype.card ι + 1) / ρ) ^ Fintype.card ι * A.card := by
  set ε := ρ / 2 ^ Fintype.card ι with hε
  have hεpos : 0 < ε := by positivity
  by_cases hne : (closureSet ε A).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp; positivity
  obtain ⟨ω₀, -⟩ := hne
  have hspos : ∀ i, (0 : ℝ) < Fintype.card (S i) := by
    intro i
    have : Nonempty (S i) := ⟨ω₀ i⟩
    exact_mod_cast Fintype.card_pos
  have hI : ∀ I : Finset ι, (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) ≤
      A.card * (1 / ε) ^ I.card := by
    intro I
    have hP : 0 < ∏ i ∈ I, (Fintype.card (S i) : ℝ) := Finset.prod_pos fun i _ => hspos i
    have key : (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) *
        (ε ^ I.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ)) ≤
        A.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by
      have hprod : (ε ^ I.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ)) =
          ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      rw [hprod]
      calc (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) *
            ∏ i ∈ I, ε * (Fintype.card (S i) : ℝ)
          ≤ ∑ x ∈ Finset.univ.filter (fun x => heavy ε A I x), ((A ∩ flat I x).card : ℝ) := by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            refine Finset.sum_le_sum fun x hx => ?_
            exact (Finset.mem_filter.1 hx).2
        _ ≤ ∑ x, ((A ∩ flat I x).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = A.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by
            have := card_inter_flat_sum A I
            exact_mod_cast this
    have hpos : 0 < ε ^ I.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have key' : (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) * ε ^ I.card *
        ∏ i ∈ I, (Fintype.card (S i) : ℝ) ≤ A.card * ∏ i ∈ I, (Fintype.card (S i) : ℝ) := by
      rw [mul_assoc]; exact key
    exact le_of_mul_le_mul_right key' hP
  have hsub : closureSet ε A ⊆ (Finset.univ : Finset (Finset ι)).biUnion
      fun I => Finset.univ.filter fun x => heavy ε A I x := by
    intro x hx
    simp only [closureSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨I, hI⟩ := hx
    rw [Finset.mem_biUnion]
    exact ⟨I, Finset.mem_univ _, by simpa using hI⟩
  calc ((closureSet ε A).card : ℝ)
      ≤ (((Finset.univ : Finset (Finset ι)).biUnion
          fun I => Finset.univ.filter fun x => heavy ε A I x).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ I : Finset ι, (((Finset.univ.filter fun x => heavy ε A I x)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ I : Finset ι, A.card * (1 / ε) ^ I.card := Finset.sum_le_sum fun I _ => hI I
    _ = A.card * (1 / ε + 1) ^ Fintype.card ι := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow (1 / ε) (1 : ℝ) (Finset.univ : Finset ι)
        rw [Finset.powerset_univ, Finset.card_univ] at this
        simpa using this
    _ ≤ ((2 ^ Fintype.card ι + 1) / ρ) ^ Fintype.card ι * A.card := by
        rw [mul_comm]
        gcongr
        rw [hε, one_div_div, div_add_one hρ.ne', ]
        gcongr

end PrivPCP.Lemma48Aux


namespace PrivPCP.Lemma48Aux

open Classical GoodQLTC

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

lemma biUnion_flat_eq (i : ι) (P : Finset (∀ i, S i)) :
    P.biUnion (fun ω => flat {i} ω) = (P.image (proj i)).biUnion (fiber i) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨ω, hω, hx⟩
    exact ⟨proj i ω, ⟨ω, hω, rfl⟩, by rw [fiber_proj]; exact hx⟩
  · rintro ⟨β, ⟨ω, hω, rfl⟩, hx⟩
    exact ⟨ω, hω, by rw [← fiber_proj]; exact hx⟩

lemma card_inter_biUnion_flat (i : ι) (P T : Finset (∀ i, S i)) :
    (T ∩ P.biUnion (fun ω => flat {i} ω)).card =
      ∑ β ∈ P.image (proj i), (T ∩ fiber i β).card := by
  rw [biUnion_flat_eq, Finset.inter_biUnion, Finset.card_biUnion]
  intro β _ β' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  simp only [fiber, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact hne (hx.2.symm.trans hx'.2)

lemma card_flat_single (i : ι) (ω : ∀ i, S i) : (flat {i} ω).card = Fintype.card (S i) := by
  rw [card_flat, Finset.prod_singleton]

/-- lines inside `B` -/
lemma card_mul_image_le (i : ι) (P B : Finset (∀ i, S i)) (hP : ∀ ω ∈ P, flat {i} ω ⊆ B) :
    Fintype.card (S i) * (P.image (proj i)).card ≤ B.card := by
  have h := card_inter_biUnion_flat i P B
  have h2 : ∀ β ∈ P.image (proj i), (B ∩ fiber i β).card = Fintype.card (S i) := by
    intro β hβ
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 hβ
    rw [fiber_proj, Finset.inter_eq_right.2 (hP ω hω), card_flat_single]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h
  rw [mul_comm, ← h]
  exact Finset.card_le_card Finset.inter_subset_left

/-- lines not inside a closed `B` -/
lemma card_out_lt {ρ : ℝ} {B : Finset (∀ i, S i)} (hB : IsClosedSet ρ B) (i : ι)
    (P : Finset (∀ i, S i)) (hP : ∀ ω ∈ P, ¬ flat {i} ω ⊆ B) :
    ((B ∩ P.biUnion (fun ω => flat {i} ω)).card : ℝ) ≤
        ρ * Fintype.card (S i) * (P.image (proj i)).card ∧
      (P.Nonempty → ((B ∩ P.biUnion (fun ω => flat {i} ω)).card : ℝ) <
        ρ * Fintype.card (S i) * (P.image (proj i)).card) := by
  rw [card_inter_biUnion_flat]
  push_cast
  have hterm : ∀ β ∈ P.image (proj i), ((B ∩ fiber i β).card : ℝ) < ρ * Fintype.card (S i) := by
    intro β hβ
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 hβ
    rw [fiber_proj]
    exact hB i ω (hP ω hω)
  have hconst : ρ * Fintype.card (S i) * ((P.image (proj i)).card : ℝ) =
      ∑ _β ∈ P.image (proj i), ρ * Fintype.card (S i) := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hconst]
  refine ⟨Finset.sum_le_sum fun β hβ => (hterm β hβ).le, fun hne => ?_⟩
  exact Finset.sum_lt_sum_of_nonempty (hne.image _) hterm

variable {F : Type} [Field F]

lemma mem_axisCode_iff (C : ∀ i, Submodule F (S i → F)) (i : ι) (x : (∀ i, S i) → F) :
    x ∈ axisCode C i ↔ ∀ b : (∀ i, S i), (fun t => x (Function.update b i t)) ∈ C i := by
  simp only [axisCode, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.funLeft_apply]
  exact Iff.rfl

lemma supportCard_eq {M : Type} [Zero M] (x : (∀ i, S i) → M) :
    supportCard x = (Finset.univ.filter fun ω => x ω ≠ 0).card := by
  unfold supportCard; congr 1

lemma lineCount_eq {M : Type} [Zero M] (i : ι) (x : (∀ i, S i) → M) :
    lineCount i x = ((Finset.univ.filter fun ω => x ω ≠ 0).image (proj i)).card := by
  unfold lineCount proj
  congr 1
  convert rfl

/-- inner part of a word along `i`-lines contained in `B` -/
noncomputable def inPart (B : Finset (∀ i, S i)) (i : ι) (z : (∀ i, S i) → F) :
    (∀ i, S i) → F :=
  fun ω => if flat {i} ω ⊆ B then z ω else 0

lemma inPart_mem {C : ∀ i, Submodule F (S i → F)} (B : Finset (∀ i, S i)) (i : ι)
    {z : (∀ i, S i) → F} (hz : z ∈ axisCode C i) : inPart B i z ∈ axisCode C i := by
  rw [mem_axisCode_iff] at hz ⊢
  intro b
  have : (fun t => inPart B i z (Function.update b i t)) =
      if flat {i} b ⊆ B then (fun t => z (Function.update b i t)) else 0 := by
    funext t
    simp only [inPart, flat_eq_of_mem (update_mem_flat b i t)]
    split_ifs <;> rfl
  rw [this]
  split_ifs
  · exact hz b
  · exact (C i).zero_mem

/-- **Lemma 17 of Kalachev–Panteleev**: closed sets are inner-generated. -/
theorem inner_generated {C : ∀ i, Submodule F (S i → F)} {ρ : ℝ}
    (hPE : IsProductExpanding ρ C) {B : Finset (∀ i, S i)} (hB : IsClosedSet ρ B) :
    ∀ n : ℕ, ∀ x ∈ ⨆ i, axisCode C i, supportCard x ≤ n → (∀ ω, x ω ≠ 0 → ω ∈ B) →
      ∃ y : ι → ((∀ i, S i) → F), (∀ i, y i ∈ axisCode C i) ∧
        (∀ i ω, y i ω ≠ 0 → flat {i} ω ⊆ B) ∧ x = ∑ i, y i := by
  intro n
  induction n with
  | zero =>
    intro x _ hx _
    refine ⟨0, fun i => Submodule.zero_mem _, fun i ω h => absurd rfl h, ?_⟩
    rw [supportCard_eq, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx
    funext ω
    simp only [Pi.zero_apply, Finset.sum_const_zero]
    by_contra h
    exact hx (Finset.mem_univ ω) h
  | succ n ih =>
    intro x hx hwt hsupp
    obtain ⟨z, hz, hxz, hbound⟩ := hPE.2 x hx
    set zin : ι → ((∀ i, S i) → F) := fun i => inPart B i (z i) with hzin
    set zout : ι → ((∀ i, S i) → F) := fun i => z i - zin i with hzout
    have hzin_mem : ∀ i, zin i ∈ axisCode C i := fun i => inPart_mem B i (hz i)
    have hzin_supp : ∀ i ω, zin i ω ≠ 0 → flat {i} ω ⊆ B := by
      intro i ω h
      by_contra h'
      exact h (by simp [hzin, inPart, h'])
    have hsplit : x = ∑ i, zin i + ∑ i, zout i := by
      rw [← Finset.sum_add_distrib, hxz]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hzout]
    by_cases hall : ∀ i ω, zout i ω = 0
    · refine ⟨zin, hzin_mem, hzin_supp, ?_⟩
      have : ∑ i, zout i = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        funext ω; exact hall i ω
      rw [hsplit, this, add_zero]
    push Not at hall
    obtain ⟨i₀, ω₀, hω₀⟩ := hall
    set x'' := ∑ i, zout i with hx''
    have hx''_mem : x'' ∈ ⨆ i, axisCode C i :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.mem_iSup_of_mem i (Submodule.sub_mem _ (hz i) (hzin_mem i))
    have hx''_supp : ∀ ω, x'' ω ≠ 0 → ω ∈ B := by
      intro ω hω
      by_contra hωB
      apply hω
      have hx0 : x ω = 0 := by
        by_contra h; exact hωB (hsupp ω h)
      have hin0 : (∑ i, zin i) ω = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_contra h
        exact hωB (hzin_supp i ω h (self_mem_flat _ _))
      have : x'' = x - ∑ i, zin i := by rw [hsplit]; ring
      rw [this, Pi.sub_apply, hx0, hin0, sub_zero]
    -- the weight bound
    set P : ι → Finset (∀ i, S i) := fun i => Finset.univ.filter fun ω => zout i ω ≠ 0 with hP
    have hPout : ∀ i, ∀ ω ∈ P i, ¬ flat {i} ω ⊆ B := by
      intro i ω hω hfl
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hω
      apply hω
      simp [hzout, hzin, inPart, hfl]
    have hPsub : ∀ i, P i ⊆ Finset.univ.filter fun ω => z i ω ≠ 0 := by
      intro i ω hω
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      intro h
      apply hω
      simp [hzout, hzin, inPart, h]
    have hsuppx'' : (Finset.univ.filter fun ω => x'' ω ≠ 0) ⊆
        Finset.univ.biUnion fun i => B ∩ (P i).biUnion (fun ω => flat {i} ω) := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      have hωB := hx''_supp ω hω
      rw [hx'', Finset.sum_apply] at hω
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hω
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, Finset.mem_inter.2 ⟨hωB, ?_⟩⟩
      rw [Finset.mem_biUnion]
      exact ⟨ω, by simpa [hP] using hi, self_mem_flat _ _⟩
    have hlt : (supportCard x'' : ℝ) < supportCard x := by
      calc (supportCard x'' : ℝ)
          ≤ ∑ i, ((B ∩ (P i).biUnion (fun ω => flat {i} ω)).card : ℝ) := by
            rw [supportCard_eq]
            exact_mod_cast (Finset.card_le_card hsuppx'').trans Finset.card_biUnion_le
        _ < ∑ i, ρ * Fintype.card (S i) * ((P i).image (proj i)).card := by
            apply Finset.sum_lt_sum
            · intro i _; exact (card_out_lt hB i (P i) (hPout i)).1
            · refine ⟨i₀, Finset.mem_univ _, (card_out_lt hB i₀ (P i₀) (hPout i₀)).2 ?_⟩
              exact ⟨ω₀, by simpa [hP] using hω₀⟩
        _ ≤ ∑ i, ρ * Fintype.card (S i) * (lineCount i (z i) : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hρ : 0 ≤ ρ := hPE.1.le
            gcongr
            rw [lineCount_eq]
            exact Finset.card_le_card (Finset.image_subset_image (hPsub i))
        _ = ρ * ∑ i, (Fintype.card (S i) : ℝ) * (lineCount i (z i) : ℝ) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ supportCard x := hbound
    have hwt'' : supportCard x'' ≤ n := by
      have : (supportCard x'' : ℝ) < n + 1 := by
        calc (supportCard x'' : ℝ) < supportCard x := hlt
          _ ≤ n + 1 := by exact_mod_cast hwt
      have : supportCard x'' < n + 1 := by exact_mod_cast this
      omega
    obtain ⟨w, hw, hwsupp, hx''w⟩ := ih x'' hx''_mem hwt'' hx''_supp
    refine ⟨fun i => zin i + w i, fun i => Submodule.add_mem _ (hzin_mem i) (hw i), ?_, ?_⟩
    · intro i ω h
      by_cases h1 : zin i ω = 0
      · simp only [Pi.add_apply, h1, zero_add] at h
        exact hwsupp i ω h
      · exact hzin_supp i ω h1
    · rw [Finset.sum_add_distrib, ← hx''w]
      exact hsplit

end PrivPCP.Lemma48Aux


open PrivPCP PrivPCP.Lemma48Aux GoodQLTC Classical

theorem solution {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : 2 ≤ r) {S : Fin r → Type}
    [∀ i, Fintype (S i)] (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1) (C : ∀ i, Submodule F (S i → F))
    (hPE : GoodQLTC.IsProductExpanding ρ C) :
    IsCollectivelyPE (ρ ^ r / (r * (2 ^ r + 1) ^ r)) C := by
  intro A _ X hX
  set Asupp : Finset (∀ i, S i) := Finset.univ.filter fun ω => (fun a => X a ω) ≠ 0 with hAsupp
  set B := closureSet (ρ / 2 ^ Fintype.card (Fin r)) Asupp with hB
  have hBc : IsClosedSet ρ B := closureSet_closed hρ.1 Asupp
  have hcard := closureSet_card (S := S) hρ.1 hρ.2 Asupp
  have hcard' : (B.card : ℝ) ≤ ((2 ^ r + 1) / ρ) ^ r * Asupp.card := by
    rw [hB]; simpa only [Fintype.card_fin] using hcard
  have hρ0 := hρ.1
  have hex : ∀ a, ∃ y : Fin r → ((∀ i, S i) → F), (∀ i, y i ∈ axisCode C i) ∧
      (∀ i ω, y i ω ≠ 0 → flat {i} ω ⊆ B) ∧ X a = ∑ i, y i := by
    intro a
    refine inner_generated hPE hBc (supportCard (X a)) (X a) (hX a) le_rfl ?_
    intro ω hω
    apply subset_closureSet
    simp only [hAsupp, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact hω (congrFun h a)
  choose Y hY1 hY2 hY3 using hex
  refine ⟨Y, hY1, hY3, ?_⟩
  have hline : ∀ i, (Fintype.card (S i) : ℝ) * (lineCountU i (fun a => Y a i) : ℝ) ≤ B.card := by
    intro i
    unfold lineCountU
    rw [lineCount_eq]
    have := card_mul_image_le i
      (Finset.univ.filter fun ω => (fun a => Y a i ω) ≠ 0) B ?_
    · exact_mod_cast this
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hω
      exact hY2 a i ω ha
  have hwt : (wtU X : ℝ) = Asupp.card := by
    unfold wtU; rw [supportCard_eq, hAsupp]
    norm_cast
  have hP : 0 ≤ ρ ^ r / (r * (2 ^ r + 1) ^ r) := by positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  calc ρ ^ r / (r * (2 ^ r + 1) ^ r) *
        ∑ i, (Fintype.card (S i) : ℝ) * (lineCountU i (fun a => Y a i) : ℝ)
      ≤ ρ ^ r / (r * (2 ^ r + 1) ^ r) * ∑ _i : Fin r, (B.card : ℝ) := by
        gcongr with i
        exact hline i
    _ = ρ ^ r / (r * (2 ^ r + 1) ^ r) * r * B.card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ ρ ^ r / (r * (2 ^ r + 1) ^ r) * r * (((2 ^ r + 1) / ρ) ^ r * Asupp.card) := by
        gcongr
    _ = Asupp.card := by
        have : (0 : ℝ) < ρ ^ r := by positivity
        have : (0 : ℝ) < 2 ^ r + 1 := by positivity
        field_simp
        rw [div_pow, mul_div_assoc', mul_div_right_comm, div_self (by positivity), one_mul]
    _ = wtU X := hwt.symm

