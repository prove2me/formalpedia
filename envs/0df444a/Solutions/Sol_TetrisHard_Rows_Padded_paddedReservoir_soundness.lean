-- Prove2me | solution 1 for TetrisHard.Rows.Padded.paddedReservoir_soundness
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:34:00.238027+00:00
-- url     : https://prove2.me/submissions/ac58bbee-c504-41bf-b492-c6e3d0dba136

import Definitions.Def_TetrisHard_Rows_PaddedGapReduction
import Definitions.Def_TetrisHard_Rows_PaddedSoundness
import Theorems.Thm_TetrisHard_Rows_Padded_paddedReservoir_chimney_reduction
import Theorems.Thm_TetrisHard_Rows_Padded_padded_initiator_and_terminator_step
import Theorems.Thm_TetrisHard_Rows_Padded_padded_filler_lg_ls_step
import Theorems.Thm_TetrisHard_Rows_Padded_padded_filler_lg_lg_sq_step
import Theorems.Thm_TetrisHard_Rows_Padded_padded_dead_trigger_eliminator

set_option autoImplicit false

namespace TetrisHard.Rows.Padded.SoundnessAssemble

open TetrisHard.Rows
open TetrisHard.Rows.Padded

lemma noRGSeqPlay_trans {R : Rotation} {s s' H' : ℕ}
    {U1 U2 U3 : Board} {ts1 ts2 : List Piece} {us1 us2 : List PieceState}
    (hp1 : NoRGSeqPlay R s s' H' U1 ts1 us1 U2)
    (hp2 : NoRGSeqPlay R s s' H' U2 ts2 us2 U3) :
    NoRGSeqPlay R s s' H' U1 (ts1 ++ ts2) (us1 ++ us2) U3 := by
  induction hp1 with
  | nil _ => simpa using hp2
  | step j ht hfr hin hy htraj _ ih =>
    exact .step j ht hfr hin hy htraj (ih hp2)

lemma noRGSeqPlay_append_split {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {ts1 ts2 : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U (ts1 ++ ts2) us U') :
    ∃ us1 us2 Umid,
      us = us1 ++ us2 ∧
      NoRGSeqPlay R s s' H' U ts1 us1 Umid ∧
      NoRGSeqPlay R s s' H' Umid ts2 us2 U' := by
  induction ts1 generalizing U us with
  | nil => exact ⟨[], us, U, rfl, .nil U, hp⟩
  | cons t ts1' ih =>
    simp only [List.cons_append] at hp
    cases hp with
    | step j ht hfr hin hy htraj hrest =>
      obtain ⟨us1, us2, Umid, rfl, hp1, hp2⟩ := ih hrest
      exact ⟨_ :: us1, us2, Umid, rfl, .step j ht hfr hin hy htraj hp1, hp2⟩

lemma allFillableStrict_of_play {R : Rotation} {s s' H' : ℕ}
    {U U' : Board} {ts : List Piece} {us : List PieceState}
    (hp : NoRGSeqPlay R s s' H' U ts us U')
    (hall : AllFillableStrict R s s' H' U') :
    AllFillableStrict R s s' H' U := by
  intro j
  obtain ⟨ts2, us2, U_end, hp2, hfull⟩ := hall j
  exact ⟨ts ++ ts2, us ++ us2, U_end, noRGSeqPlay_trans hp hp2, hfull⟩

lemma filler_step {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {U U' : Board} {us : List PieceState}
    {j₀ : Fin s} {h₀ : ℕ} {h : Fin s → ℕ}
    (hof : OneOverflatState U s H' j₀ h₀ h)
    (hp : NoRGSeqPlay R s s' H' U filler us U')
    (hall : AllFillableStrict R s s' H' U') :
    OneOverflatState U' s H' j₀ (h₀ + 6) h ∨
      ∃ j_dp : Fin s, DeadTriggerState U' s H' j_dp j₀ (h₀ + 4) h := by
  have hfeq : filler = [.LG, .LS] ++ [.LG, .LG, .Sq] := rfl
  rw [hfeq] at hp
  obtain ⟨us1, us2, U₂, _, hp1, hp2⟩ := noRGSeqPlay_append_split hp
  have hall2 := allFillableStrict_of_play hp2 hall
  obtain ⟨hth2, hunp2⟩ := padded_filler_lg_ls_step R hReason s s' H' hs_le U U₂ us1 j₀ h₀ h hof hp1 hall2
  exact padded_filler_lg_lg_sq_step R hReason s s' H' hs_le U₂ U' us2 j₀ (h₀ + 4) h hth2 hunp2 hp2 hall

lemma filler_chain {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') :
    ∀ (m : ℕ) {U U' : Board} {us : List PieceState} {j₀ : Fin s} {h₀ : ℕ} {h : Fin s → ℕ},
      OneOverflatState U s H' j₀ h₀ h →
      NoRGSeqPlay R s s' H' U ((List.replicate m filler).flatten ++ terminator) us U' →
      AllFillableStrict R s s' H' U' →
      AllUnpreppedHeights U' s H' (Function.update h j₀ (h₀ + 6 * m + 4))
  | 0, U, U', us, j₀, h₀, h, hof, hp, hall => by
      simp only [List.replicate_zero, List.flatten_nil, List.nil_append, Nat.mul_zero,
        Nat.add_zero] at hp ⊢
      exact (padded_initiator_and_terminator_step R hReason s s' H' hs_le).2 U U' us j₀ h₀ h hof hp hall
  | m + 1, U, U', us, j₀, h₀, h, hof, hp, hall => by
      simp only [List.replicate_succ, List.flatten_cons, List.append_assoc] at hp
      obtain ⟨us1, us2, U_mid, _, hp_fil, hp_rest⟩ := noRGSeqPlay_append_split hp
      have hall_mid := allFillableStrict_of_play hp_rest hall
      rcases filler_step hReason hs_le hof hp_fil hall_mid with hof_mid | ⟨j_dp, hdt_mid⟩
      · have ih := filler_chain hReason hs_le m hof_mid hp_rest hall
        have heq : (h₀ + 6) + 6 * m + 4 = h₀ + 6 * (m + 1) + 4 := by omega
        rwa [heq] at ih
      · exfalso
        have hkill := padded_dead_trigger_eliminator R hReason s s' H' hs_le
        cases m with
        | zero =>
          simp only [List.replicate_zero, List.flatten_nil, List.nil_append] at hp_rest
          exact hkill.1 U_mid U' [] us2 j_dp j₀ (h₀ + 4) h hdt_mid hp_rest hall
        | succ m' =>
          simp only [List.replicate_succ, List.flatten_cons] at hp_rest
          have hcons : filler ++ (List.replicate m' filler).flatten ++ terminator =
              .LG :: .LS :: ([.LG, .LG, .Sq] ++ (List.replicate m' filler).flatten ++ terminator) := rfl
          rw [hcons] at hp_rest
          exact hkill.2 U_mid U' _ us2 j_dp j₀ (h₀ + 4) h hdt_mid hp_rest hall

lemma integerBlock_step {R : Rotation} (hReason : Reasonable R)
    {s s' H' : ℕ} (hs_le : s ≤ s') {a : ℕ} {U U' : Board} {us : List PieceState} {h : Fin s → ℕ}
    (hunp : AllUnpreppedHeights U s H' h)
    (hp : NoRGSeqPlay R s s' H' U (integerBlock a) us U')
    (hall : AllFillableStrict R s s' H' U') :
    ∃ j₀ : Fin s, AllUnpreppedHeights U' s H' (Function.update h j₀ (h j₀ + (6 * a + 6))) := by
  have hbeq : integerBlock a = initiator ++ ((List.replicate a filler).flatten ++ terminator) := by
    simp [integerBlock, List.append_assoc]
  rw [hbeq] at hp
  obtain ⟨us1, us2, U_mid, _, hp_init, hp_tail⟩ := noRGSeqPlay_append_split hp
  obtain ⟨j₀, hof_mid⟩ := (padded_initiator_and_terminator_step R hReason s s' H' hs_le).1
    U U_mid us1 h hunp hp_init (allFillableStrict_of_play hp_tail hall)
  have hfin := filler_chain hReason hs_le a hof_mid hp_tail hall
  have heq : (h j₀ + 2) + 6 * a + 4 = h j₀ + (6 * a + 6) := by omega
  rw [heq] at hfin
  exact ⟨j₀, hfin⟩

lemma integerBlock_list_step {R : Rotation} (hReason : Reasonable R)
    {P : ThreePartition} (hs : 0 < P.s) {s' H' : ℕ} (hs_le : P.s ≤ s') :
    ∀ (L : List (Fin (3 * P.s))), L.Nodup →
      ∀ {U U' : Board} {us : List PieceState} {h : Fin P.s → ℕ},
        AllUnpreppedHeights U P.s H' h →
        NoRGSeqPlay R P.s s' H' U (L.flatMap fun i => integerBlock (P.entry i)) us U' →
        AllFillableStrict R P.s s' H' U' →
        ∃ assign : Fin (3 * P.s) → Fin P.s,
          AllUnpreppedHeights U' P.s H' (fun j =>
            h j + ∑ i ∈ L.toFinset.filter (fun i => assign i = j), (6 * P.entry i + 6))
  | [], _, _, _, _, h, hunp, hp, _ => by
      simp only [List.flatMap_nil] at hp
      cases hp
      refine ⟨fun _ => ⟨0, hs⟩, fun j => ?_⟩
      simpa using hunp j
  | i₀ :: L', hnd, U, U', us, h, hunp, hp, hall => by
      rw [List.nodup_cons] at hnd
      rcases hnd with ⟨hi0_not_mem, hnd'⟩
      simp only [List.flatMap_cons] at hp
      obtain ⟨_, _, U_mid, _, hp_blk, hp_rest⟩ := noRGSeqPlay_append_split hp
      obtain ⟨j₀, hunp_mid⟩ := integerBlock_step hReason hs_le hunp hp_blk
        (allFillableStrict_of_play hp_rest hall)
      obtain ⟨assign', hunp_end⟩ :=
        integerBlock_list_step hReason hs hs_le L' hnd' hunp_mid hp_rest hall
      refine ⟨Function.update assign' i₀ j₀, fun j => ?_⟩
      have hfilt_rest :
          L'.toFinset.filter (fun i => Function.update assign' i₀ j₀ i = j) =
            L'.toFinset.filter (fun i => assign' i = j) := by
        apply Finset.filter_congr
        intro i hi
        have hne : i ≠ i₀ := fun he => hi0_not_mem (he ▸ List.mem_toFinset.mp hi)
        rw [Function.update_of_ne hne]
      have hi0_not_fin : i₀ ∉ L'.toFinset := mt List.mem_toFinset.mp hi0_not_mem
      have hheq :
          Function.update h j₀ (h j₀ + (6 * P.entry i₀ + 6)) j +
              ∑ i ∈ L'.toFinset.filter (fun i => assign' i = j), (6 * P.entry i + 6) =
            h j + ∑ i ∈ (i₀ :: L').toFinset.filter (fun i => Function.update assign' i₀ j₀ i = j),
              (6 * P.entry i + 6) := by
        rw [List.toFinset_cons, Finset.filter_insert]
        by_cases hj : j₀ = j
        · subst hj
          simp only [Function.update_self, ↓reduceIte, hfilt_rest]
          rw [Finset.sum_insert (mt (fun hm => (Finset.mem_filter.mp hm).1) hi0_not_fin)]
          omega
        · have hj' : j ≠ j₀ := Ne.symm hj
          simp only [Function.update_self, hj, ↓reduceIte, Function.update_of_ne hj', hfilt_rest]
      dsimp only [AllUnpreppedHeights] at hunp_end ⊢
      rw [← hheq]
      exact hunp_end j

lemma numberPieces_eq_finRange (P : ThreePartition) :
    numberPieces P = (List.finRange (3 * P.s)).flatMap (fun i => integerBlock (P.entry i)) := by
  have hof : List.ofFn P.entry = (List.finRange (3 * P.s)).map P.entry := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2; simp
  unfold numberPieces
  rw [hof, List.flatMap_map]

lemma two_le_s_of_not_hasSolution {P : ThreePartition} (hP : P.Valid) (hs : 0 < P.s)
    (hno : ¬ P.HasSolution) : 2 ≤ P.s := by
  by_contra hlt
  have hs1 : P.s = 1 := by omega
  apply hno
  refine ⟨fun _ => ⟨0, by omega⟩, fun j => ?_⟩
  have hj : j = ⟨0, by omega⟩ := by ext; omega
  subst hj
  have hfilt : (Finset.univ.filter fun _ : Fin (3 * P.s) => (⟨0, by omega⟩ : Fin P.s) = ⟨0, by omega⟩) =
      Finset.univ := by simp
  rw [hfilt, hP.1, hs1, one_mul]

theorem hasSolution_of_phase1_bucketFull {R : Rotation} (hReason : Reasonable R)
    {P : ThreePartition} (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (hno : ¬ P.HasSolution)
    {pad K st r : ℕ}
    (hunp0 : AllUnpreppedHeights (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
      P.s (12 * pad + baseHeight P) (fun _ => 12 * pad + 4))
    {us us_I : List PieceState} {U_num U_end : Board}
    (hseq_num : NoRGSeqPlay R P.s (P.s + pad) (12 * pad + baseHeight P)
      (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
      (numberPieces P) us U_num)
    (hseq_I : NoRGSeqPlay R P.s (P.s + pad) (12 * pad + baseHeight P)
      U_num (List.replicate P.s .I) us_I U_end)
    (hall_full : ∀ j : Fin P.s, BucketFull U_end j.val (12 * pad + baseHeight P)) :
    False := by
  set H' := 12 * pad + baseHeight P
  have hs2 : 2 ≤ P.s := two_le_s_of_not_hasSolution hP hs hno
  have hall_num : AllFillableStrict R P.s (P.s + pad) H' U_num :=
    fun j => ⟨List.replicate P.s .I, us_I, U_end, hseq_I, hall_full j⟩
  rw [numberPieces_eq_finRange P] at hseq_num
  obtain ⟨assign, hunp_fin⟩ := integerBlock_list_step hReason hs (by omega : P.s ≤ P.s + pad)
    (List.finRange (3 * P.s)) (List.nodup_finRange _) hunp0 hseq_num hall_num
  have hfinRange_finset : (List.finRange (3 * P.s)).toFinset = Finset.univ := by
    ext i; simp
  set h_fin : Fin P.s → ℕ := fun j =>
    (12 * pad + 4) + ∑ i ∈ Finset.univ.filter (fun i => assign i = j), (6 * P.entry i + 6)
  have hunp_fin' : ∀ j : Fin P.s, UnpreppedAt U_num j.val H' (h_fin j) := by
    intro j
    have hj := hunp_fin j
    rwa [hfinRange_finset] at hj
  have hfin_le : ∀ j : Fin P.s, h_fin j ≤ H' := fun j => by
    rcases hunp_fin' j with ⟨_, _, hle, _⟩
    exact hle
  have hpart : (∑ j : Fin P.s,
      ∑ i ∈ Finset.univ.filter (fun i => assign i = j), (6 * P.entry i + 6)) =
      ∑ i : Fin (3 * P.s), (6 * P.entry i + 6) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hsum_items : (∑ i : Fin (3 * P.s), (6 * P.entry i + 6)) = P.s * (6 * P.target + 18) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hsum_eq : ∑ j : Fin P.s, h_fin j = ∑ _j : Fin P.s, H' := by
    dsimp only [h_fin]
    rw [Finset.sum_add_distrib, hpart, hsum_items]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, H', baseHeight]
    ring
  have hall_eq : ∀ j : Fin P.s, h_fin j = H' := by
    intro j0
    have hle0 := hfin_le j0
    by_contra hne
    have hlt0 : h_fin j0 < H' := by omega
    have hrest : ∑ j ∈ Finset.univ.erase j0, h_fin j ≤ ∑ _j ∈ Finset.univ.erase j0, H' :=
      Finset.sum_le_sum fun j _ => hfin_le j
    have h1 := Finset.add_sum_erase Finset.univ h_fin (Finset.mem_univ j0)
    have h2 := Finset.add_sum_erase Finset.univ (fun _ : Fin P.s => H') (Finset.mem_univ j0)
    omega
  apply hno
  refine ⟨assign, fun j => ?_⟩
  set A := Finset.univ.filter (fun i => assign i = j)
  have hj_eq : (12 * pad + 4) + (6 * (∑ i ∈ A, P.entry i) + 6 * A.card) =
      12 * pad + (6 * P.target + 22) := by
    have h0 : (12 * pad + 4) + ∑ i ∈ A, (6 * P.entry i + 6) = 12 * pad + (6 * P.target + 22) :=
      hall_eq j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at h0
    omega
  have hsum_card : (∑ i ∈ A, P.entry i) + A.card = P.target + 3 := by omega
  have hcard_le : A.card ≤ 3 * P.s := by
    have hsub : A.card ≤ (Finset.univ : Finset (Fin (3 * P.s))).card := Finset.card_le_univ A
    simpa using hsub
  by_contra hne_t
  have hgap_ge := hN.2.2 A hne_t
  have hcast : (∑ i ∈ A, (P.entry i : ℤ)) = ((∑ i ∈ A, P.entry i : ℕ) : ℤ) :=
    (Nat.cast_sum A P.entry).symm
  rw [hcast] at hgap_ge
  rcases abs_cases ((P.target : ℤ) - ((∑ i ∈ A, P.entry i : ℕ) : ℤ)) with ⟨habs, _⟩ | ⟨habs, _⟩ <;>
    omega

end TetrisHard.Rows.Padded.SoundnessAssemble

theorem solution
    (R : TetrisHard.Rows.Rotation) (hR : R.Admissible) (hReason : TetrisHard.Rows.Reasonable R)
    (P : TetrisHard.Rows.ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (hno : ¬ P.HasSolution)
    (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad)
    (hK : TetrisHard.Rows.Padded.maxJump R + 2 ≤ K)
    (hst : 5 * max R.radius 2 + 12 ≤ st) :
    ∀ v, TetrisHard.Rows.Attainable R (TetrisHard.Rows.Padded.paddedReservoirGame P pad K st r) v →
      v ≤ TetrisHard.Rows.Padded.paddedNoBound P pad K st := by
  intro v hatt
  rcases TetrisHard.Rows.Padded.paddedReservoir_chimney_reduction
      R hR hReason P hP hN hs pad K st r hpad hK hst v hatt with
    hle | ⟨hunp0, us, us_I, U_num, U_end, hseq_num, hseq_I, hall_full⟩
  · exact hle
  · exact False.elim (TetrisHard.Rows.Padded.SoundnessAssemble.hasSolution_of_phase1_bucketFull
      hReason hP hN hs hno hunp0 hseq_num hseq_I hall_full)
