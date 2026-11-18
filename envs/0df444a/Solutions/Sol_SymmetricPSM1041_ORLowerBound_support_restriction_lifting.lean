-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.support_restriction_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:54:25.848238+00:00
-- url     : https://prove2.me/submissions/533913ad-3b91-43f7-a189-7677117fc2b8

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions

open SymmetricPSM1041.ORLowerBound

private lemma individualSupport_surjective {ι : Type*} (g : (ι → Bool) → Bool) (B : ℕ)
    (h : IndividualLowerBound .support g (B + 1)) : Function.Surjective g := by
  classical
  have hnonconst : ¬ ∃ b, ∀ x, g x = b := by
    rintro ⟨b, hb⟩
    let Q : PSM ι := {
      seedCount := 1
      seedCount_pos := by omega
      alphabet := fun _ => {[]}
      message := fun _ _ _ => ⟨[], by simp⟩
      decode := fun _ => b }
    have hcorrect : PerfectCorrect Q g := by
      intro x r
      simp [Q, hb x]
    have hprivate : SupportPrivate Q g := by
      intro x y hxy
      apply Set.ext
      intro t
      simp only [transcriptSupport, Set.mem_range]
      constructor <;> rintro ⟨r, rfl⟩
      · exact ⟨r, by funext i; apply Subtype.ext; rfl⟩
      · exact ⟨r, by funext i; apply Subtype.ext; rfl⟩
    obtain ⟨i, hi⟩ := h Q hcorrect hprivate
    have hcard : (localAlphabet Q i).card = 1 := by
      have halpha : localAlphabet Q i = {[]} := by
        ext w
        simp [localAlphabet, Q]
      simp [halpha]
    rw [hcard] at hi
    have : 1 < 2 ^ (B + 1) := Nat.one_lt_two_pow (by omega)
    omega
  intro b
  by_cases hb : b = false
  · subst b
    by_contra hno
    apply hnonconst
    refine ⟨true, ?_⟩
    intro x
    cases hx : g x <;> simp_all
  · have hb' : b = true := by cases b <;> simp_all
    subst b
    by_contra hno
    apply hnonconst
    refine ⟨false, ?_⟩
    intro x
    cases hx : g x <;> simp_all

theorem solution {n : ℕ} (f : (Fin n → Bool) → Bool)
    (s B : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hrestr : ∀ I : Finset (Fin n), s ≤ I.card → ∃ z : Fin n → Bool,
      IndividualLowerBound .support (restrictFunction f I z) (B + 1)) :
    ∀ P : PSM (Fin n), PerfectCorrect P f → SupportPrivate P f →
      ∃ (x : Fin n → Bool) (r : Fin P.seedCount),
        (B + 1) * (n - s + 1) ≤ transcriptLength P x r := by
  classical
  intro P hc hp
  let longSet (x : Fin n → Bool) (r : Fin P.seedCount) : Finset (Fin n) :=
    Finset.univ.filter fun i => B < (P.message i (x i) r).val.length
  let pairs := ((Finset.univ : Finset (Fin n → Bool)).product
    (Finset.univ : Finset (Fin P.seedCount)))
  have hpairs : pairs.Nonempty := by
    refine ⟨(fun _ => false, ⟨0, P.seedCount_pos⟩), ?_⟩
    simp [pairs]
  obtain ⟨xr, hxrmem, hxrmax⟩ := Finset.exists_max_image pairs
    (fun xr => (longSet xr.1 xr.2).card) hpairs
  let x₀ := xr.1
  let r₀ := xr.2
  let L := (B + 1) * (n - s + 1)
  by_contra hnone
  push_neg at hnone
  have long_bound (x : Fin n → Bool) (r : Fin P.seedCount) :
      (longSet x r).card ≤ n - s := by
    by_contra hbad
    have hlen : (B + 1) * (longSet x r).card ≤ transcriptLength P x r := by
      calc
        (B + 1) * (longSet x r).card = ∑ _i ∈ longSet x r, (B + 1) := by
          simp [mul_comm]
        _ ≤ ∑ i ∈ longSet x r, (P.message i (x i) r).val.length := by
          apply Finset.sum_le_sum
          intro i hi
          have := Finset.mem_filter.1 hi |>.2
          omega
        _ ≤ ∑ i, (P.message i (x i) r).val.length := by
          exact Finset.sum_le_sum_of_subset (by simp [longSet])
        _ = transcriptLength P x r := rfl
    have hcount : n - s + 1 ≤ (longSet x r).card := by omega
    have : L ≤ transcriptLength P x r := by
      dsimp [L]
      exact (Nat.mul_le_mul_left (B + 1) hcount).trans hlen
    exact (not_lt_of_ge this) (hnone x r)
  let I : Finset (Fin n) := Finset.univ.filter fun i => i ∉ longSet x₀ r₀
  have hIcard : s ≤ I.card := by
    have hpartition : I.card + (longSet x₀ r₀).card = n := by
      have hIeq : I = (Finset.univ : Finset (Fin n)) \ longSet x₀ r₀ := by
        ext i
        simp [I]
      rw [hIeq]
      simpa using Finset.card_sdiff_add_card_eq_card
        (s := longSet x₀ r₀) (t := (Finset.univ : Finset (Fin n))) (by simp)
    have := long_bound x₀ r₀
    omega
  obtain ⟨z, hz⟩ := hrestr I hIcard
  let g := restrictFunction f I z
  let v : Transcript P := transcript P x₀ r₀
  obtain ⟨y₀, hy₀⟩ := (individualSupport_surjective g B hz) (P.decode v)
  let extend (y : I → Bool) : Fin n → Bool :=
    fun i => if hi : i ∈ I then y ⟨i, hi⟩ else z i
  have extend_eq (y : I → Bool) :
      (fun i => if hi : i ∈ I then y ⟨i, hi⟩ else z i) = extend y := by
    funext i
    by_cases hi : i ∈ I <;> simp [extend, hi]
  have g_eq (y : I → Bool) : g y = f (extend y) := by
    dsimp [g, restrictFunction]
    congr 1
    funext i
    by_cases hi : i ∈ I <;> simp [extend, hi]
  have hfy₀ : f (extend y₀) = f x₀ := by
    have h1 : f (extend y₀) = P.decode v := (g_eq y₀).symm.trans hy₀
    have h2 : P.decode v = f x₀ := hc x₀ r₀
    exact h1.trans h2
  let seedSet : Finset (Fin P.seedCount) := Finset.univ.filter fun r =>
    ∀ i : Fin n, i ∉ I → P.message i (z i) r = v i
  have hseedSet : seedSet.Nonempty := by
    have hsupp := hp x₀ (extend y₀) hfy₀.symm
    have hv : v ∈ transcriptSupport P x₀ := ⟨r₀, rfl⟩
    rw [hsupp] at hv
    obtain ⟨r, hr⟩ := hv
    refine ⟨r, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    intro i hi
    have hri := congrFun hr i
    simpa [transcript, extend, hi] using hri
  let seedEquiv : Fin seedSet.card ≃o seedSet := seedSet.orderIsoOfFin rfl
  let oldSeed : Fin seedSet.card → Fin P.seedCount := fun r => (seedEquiv r).1
  have oldSeed_mem (r : Fin seedSet.card) : oldSeed r ∈ seedSet := by
    exact seedSet.orderEmbOfFin_mem rfl r
  let fill (t : (i : I) → {w : Message // w ∈ P.alphabet i.1}) : Transcript P :=
    fun i => if hi : i ∈ I then t ⟨i, hi⟩ else v i
  let Q : PSM I := {
    seedCount := seedSet.card
    seedCount_pos := Finset.card_pos.mpr hseedSet
    alphabet := fun i => P.alphabet i.1
    message := fun i b r => P.message i.1 b (oldSeed r)
    decode := fun t => P.decode (fill t) }
  have event_spec (r : Fin seedSet.card) (i : Fin n) (hi : i ∉ I) :
      P.message i (z i) (oldSeed r) = v i := by
    exact (Finset.mem_filter.1 (oldSeed_mem r)).2 i hi
  have hQcorrect : PerfectCorrect Q g := by
    intro y r
    have htr : fill (transcript Q y r) = transcript P (extend y) (oldSeed r) := by
      funext i
      by_cases hi : i ∈ I
      · simp [fill, transcript, Q, extend, hi]
      · simp [fill, transcript, Q, extend, hi, event_spec r i hi]
    change P.decode (fill (transcript Q y r)) = g y
    rw [htr, hc]
    exact (g_eq y).symm
  let seed_of_mem (r : Fin P.seedCount) (hr : r ∈ seedSet) : Fin seedSet.card :=
    seedEquiv.symm ⟨r, hr⟩
  have oldSeed_seed_of_mem (r : Fin P.seedCount) (hr : r ∈ seedSet) :
      oldSeed (seed_of_mem r hr) = r := by
    change (seedEquiv (seedEquiv.symm ⟨r, hr⟩)).1 = r
    exact congrArg Subtype.val (seedEquiv.apply_symm_apply ⟨r, hr⟩)
  have hQprivate : SupportPrivate Q g := by
    intro y y' hgy
    apply Set.ext
    intro t
    constructor
    · rintro ⟨r, rfl⟩
      have hfull : f (extend y) = f (extend y') := by
        exact (g_eq y).symm.trans (hgy.trans (g_eq y'))
      have hsupp := hp (extend y) (extend y') hfull
      have hvfull : transcript P (extend y) (oldSeed r) ∈ transcriptSupport P (extend y) :=
        ⟨oldSeed r, rfl⟩
      rw [hsupp] at hvfull
      obtain ⟨r', hr'⟩ := hvfull
      have hr'mem : r' ∈ seedSet := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        have hout := congrFun hr' i
        simpa [transcript, extend, hi, event_spec r i hi] using hout
      refine ⟨seed_of_mem r' hr'mem, ?_⟩
      funext i
      apply Subtype.ext
      have hin := congrFun hr' i.1
      have hin' := congrArg Subtype.val hin
      simpa [transcript, Q, extend, i.2, oldSeed_seed_of_mem r' hr'mem] using hin'
    · rintro ⟨r, rfl⟩
      have hfull : f (extend y') = f (extend y) := by
        exact (g_eq y').symm.trans (hgy.symm.trans (g_eq y))
      have hsupp := hp (extend y') (extend y) hfull
      have hvfull : transcript P (extend y') (oldSeed r) ∈ transcriptSupport P (extend y') :=
        ⟨oldSeed r, rfl⟩
      rw [hsupp] at hvfull
      obtain ⟨r', hr'⟩ := hvfull
      have hr'mem : r' ∈ seedSet := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        have hout := congrFun hr' i
        simpa [transcript, extend, hi, event_spec r i hi] using hout
      refine ⟨seed_of_mem r' hr'mem, ?_⟩
      funext i
      apply Subtype.ext
      have hin := congrFun hr' i.1
      have hin' := congrArg Subtype.val hin
      simpa [transcript, Q, extend, i.2, oldSeed_seed_of_mem r' hr'mem] using hin'
  obtain ⟨i, hi⟩ := hz Q hQcorrect hQprivate
  have hexists_long : ∃ b r, B < (Q.message i b r).val.length := by
    by_contra hshort
    push_neg at hshort
    let U : Finset (List Bool) := (Finset.range (B + 1)).biUnion fun d =>
      Finset.univ.image (fun v : List.Vector Bool d => v.1)
    have hsubU : localAlphabet Q i ⊆ U := by
      intro w hw
      simp only [localAlphabet, Finset.mem_image] at hw
      obtain ⟨br, -, rfl⟩ := hw
      have hlen := hshort br.1 br.2
      apply Finset.mem_biUnion.2
      refine ⟨(Q.message i br.1 br.2).val.length, by simp [hlen], ?_⟩
      apply Finset.mem_image.2
      exact ⟨⟨(Q.message i br.1 br.2).val, rfl⟩, Finset.mem_univ _, rfl⟩
    have hUcard : U.card ≤ 2 ^ (B + 1) - 1 := by
      calc
        U.card ≤ ∑ d ∈ Finset.range (B + 1),
            (Finset.univ.image (fun v : List.Vector Bool d => v.1)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ d ∈ Finset.range (B + 1), 2 ^ d := by
          apply Finset.sum_le_sum
          intro d hd
          calc
            _ ≤ (Finset.univ : Finset (List.Vector Bool d)).card := Finset.card_image_le
            _ = 2 ^ d := by simp
        _ = 2 ^ (B + 1) - 1 := by
          simpa using geom_sum_mul_of_one_le (x := (2 : ℕ)) (by omega) (B + 1)
    have hcardle := Finset.card_le_card hsubU |>.trans hUcard
    have hlt : 2 ^ (B + 1) - 1 < 2 ^ (B + 1) :=
      Nat.sub_lt (pow_pos (by omega) _) (by omega)
    exact (not_lt_of_ge hi) (hcardle.trans_lt hlt)
  obtain ⟨b, r, hlong⟩ := hexists_long
  let x' : Fin n → Bool := extend (fun j => if j = i then b else false)
  let r' : Fin P.seedCount := oldSeed r
  have houtside (j : Fin n) (hj : j ∉ I) : P.message j (x' j) r' = v j := by
    simp [x', extend, hj, r', event_spec r j hj]
  have hlong_old (j : Fin n) (hj : j ∈ longSet x₀ r₀) :
      j ∈ longSet x' r' := by
    have hjI : j ∉ I := by simp [I, hj]
    have hvj := houtside j hjI
    have hjlong := Finset.mem_filter.1 hj |>.2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [longSet, v, transcript] using hvj.symm ▸ hjlong
  have hinew : i.1 ∈ longSet x' r' := by
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [Q, x', extend, i.2, r'] using hlong
  have hinew_not : i.1 ∉ longSet x₀ r₀ := by
    have hiI := i.2
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hiI
    exact hiI
  have hstrict : (longSet x₀ r₀).card < (longSet x' r').card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hlong_old, by
      intro heq
      exact hinew_not (heq ▸ hinew)⟩)
  have hmax := hxrmax (x', r') (by simp [pairs])
  exact (not_lt_of_ge hmax) hstrict
