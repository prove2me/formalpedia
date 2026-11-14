-- Prove2me | solution 1 for SaglamGV.exists_row_of_no_odd_circuit
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T12:35:05.447419+00:00
-- url     : https://prove2.me/submissions/a776577c-6fed-4079-9e4b-04813fc59217

import Theorems.Thm_SaglamGV_circuit_sum_rank
set_option autoImplicit false
open Finset Matrix Submodule SaglamGV

private lemma even_zero_sum (n d m : ℕ) (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (hZ : oddCircuitCount d M = 0) (T : Finset (Fin n → ZMod 2))
    (hTK : T ⊆ kerSet d M) (hT : ∑ x ∈ T, x = 0) : Even T.card := by
  classical
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    by_cases hTe : T = ∅
    · simp [hTe]
    have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTe
    have hdep : ¬ LinearIndepOn (ZMod 2) id (T : Set (Fin n → ZMod 2)) := by
      intro hli
      obtain ⟨x, hx⟩ := hTne
      have h := (linearIndepOn_finset_iff (R := ZMod 2) (v := id) (s := T)).mp hli
        (fun _ ↦ 1) (by simpa using hT) x hx
      exact one_ne_zero h
    obtain ⟨C, hCT, hmin⟩ := exists_minimal_le_of_wellFoundedLT
      (fun C : Finset (Fin n → ZMod 2) ↦
        ¬ LinearIndepOn (ZMod 2) id (C : Set (Fin n → ZMod 2))) T hdep
    have hC : IsCircuit C := by
      refine ⟨hmin.1, ?_⟩
      intro U hUC
      by_contra hU
      exact hUC.2 (hmin.2 hU hUC.le)
    have hCK : C ⊆ kerSet d M := hCT.trans hTK
    have hCb : C ⊆ ballP n d := fun x hx ↦ (Finset.mem_filter.mp (hCK hx)).1
    have hc : C ∈ circuits n d C.card := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hCb, hC⟩, rfl⟩
    have hstr := SaglamGV.circuit_sum_rank n d C.card C hc
    have hCeven : Even C.card := by
      apply Nat.not_odd_iff_even.mp
      intro ho
      have hmem : C ∈ (allCircuits n d).filter
          (fun S ↦ S ⊆ kerSet d M ∧ Odd S.card) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, hCK, ho⟩
      have he := Finset.card_eq_zero.mp hZ
      rw [he] at hmem
      exact Finset.notMem_empty _ hmem
    have hCne : C.Nonempty := Finset.card_pos.mp (by have := hstr.2.2.1; omega)
    have hlt : T \ C ⊂ T := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro he
      obtain ⟨x, hx⟩ := hCne
      have hxT := hCT hx
      have hxc : x ∈ T \ C := he.symm ▸ hxT
      exact (Finset.mem_sdiff.mp hxc).2 hx
    have hrem : ∑ x ∈ T \ C, x = 0 := by
      have h := Finset.sum_sdiff (f := fun x ↦ x) hCT
      simpa only [hT, hstr.1, add_zero] using h
    have heRem := ih (T \ C) hlt (Finset.sdiff_subset.trans hTK) hrem
    have hcard := Finset.card_sdiff_add_card_eq_card hCT
    rw [← hcard]
    exact heRem.add hCeven


private lemma functional_on_K (n d m : ℕ) (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (hZ : oddCircuitCount d M = 0) :
    ∃ f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∀ x ∈ kerSet d M, f x = 1 := by
  classical
  let K := kerSet d M
  let U := Submodule.span (ZMod 2)
    ((fun x : Fin n → ZMod 2 ↦ (x, (1 : ZMod 2))) '' (K : Set (Fin n → ZMod 2)))
  have hnot : ((0 : Fin n → ZMod 2), (1 : ZMod 2)) ∉ U := by
    intro h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := ZMod 2)).mp h
    have hfirst : ∑ x ∈ K, c x • x = 0 := by
      simpa [Prod.fst_sum] using congrArg Prod.fst hc
    have hsecond : ∑ x ∈ K, c x = 1 := by
      simpa [smul_eq_mul, Prod.snd_sum] using congrArg Prod.snd hc
    let T := K.filter (fun x ↦ c x ≠ 0)
    have hc1 (x : Fin n → ZMod 2) (hx : c x ≠ 0) : c x = 1 :=
      (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) (c x) hx
    have hsum : ∑ x ∈ T, x = 0 := by
      calc
        _ = ∑ x ∈ K, c x • x := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : c x = 0
          · simp [hx]
          · simp [hc1 x hx]
        _ = 0 := hfirst
    have hcard : (T.card : ZMod 2) = ∑ x ∈ K, c x := by
      rw [Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : c x = 0
      · simp [hx]
      · simp [hc1 x hx]
    have heven := even_zero_sum n d m M hZ T (Finset.filter_subset _ _) hsum
    obtain ⟨k, hk⟩ := heven
    have hz : (T.card : ZMod 2) = 0 := by
      rw [hk, Nat.cast_add, CharTwo.add_self_eq_zero]
    exact zero_ne_one (hz.symm.trans (hcard.trans hsecond))
  obtain ⟨f, hfe, hfU⟩ := U.exists_le_ker_of_notMem hnot
  have hf1 : f ((0 : Fin n → ZMod 2), (1 : ZMod 2)) = 1 :=
    (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hfe
  refine ⟨f.comp (LinearMap.inl (ZMod 2) (Fin n → ZMod 2) (ZMod 2)), ?_⟩
  intro x hx
  have hfx : f (x, (1 : ZMod 2)) = 0 :=
    hfU (Submodule.subset_span (Set.mem_image_of_mem _ hx))
  have ha : f (x, (0 : ZMod 2)) + 1 = 0 := by
    rw [← hf1, ← map_add]
    simpa using hfx
  have hvalue : f (x, (0 : ZMod 2)) = -(1 : ZMod 2) := eq_neg_of_add_eq_zero_left ha
  simpa [CharTwo.neg_eq] using hvalue

private lemma dual_as_row (n : ℕ) (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ v : Fin n → ZMod 2, ∀ x, dot v x = f x := by
  classical
  let v := fun i : Fin n ↦ f (Pi.single i 1)
  refine ⟨v, ?_⟩
  intro x
  have hrep : ∑ i, x i • (Pi.single i 1 : Fin n → ZMod 2) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    dot v x = ∑ i, x i * f (Pi.single i 1) := by simp [dot, v, mul_comm]
    _ = f (∑ i, x i • (Pi.single i 1 : Fin n → ZMod 2)) := by
      simp [map_sum, map_smul, smul_eq_mul]
    _ = f x := congrArg f hrep

private lemma appended_dist (n d m : ℕ) (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) (hv : ∀ x ∈ kerSet d M, dot v x = 1) :
    HasDistAtLeast (parityCode (appendRow M v)) d := by
  intro x hx hx0
  by_contra hd
  have hxnorm : 0 < hammingNorm x := hammingNorm_pos_iff.mpr hx0
  have hHx : appendRow M v *ᵥ x = 0 := hx
  have hMx : M *ᵥ x = 0 := by
    ext i
    have hi := congrFun hHx (Fin.castSucc i)
    simpa [appendRow, Matrix.mulVec] using hi
  have hdot : dot v x = 0 := by
    have hi := congrFun hHx (Fin.last m)
    simpa [appendRow, Matrix.mulVec, dot, dotProduct] using hi
  have hxK : x ∈ kerSet d M := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hxnorm, by omega⟩, hMx⟩
  exact zero_ne_one (hdot.symm.trans (hv x hxK))

private lemma code_size (n r : ℕ) (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    2 ^ n ≤ 2 ^ r * Nat.card (parityCode H) := by
  have hnull := H.mulVecLin.finrank_range_add_finrank_ker
  have hrange := (LinearMap.range H.mulVecLin).finrank_le
  simp only [Module.finrank_pi, Fintype.card_fin] at hnull hrange
  have hk : n ≤ r + Module.finrank (ZMod 2) (LinearMap.ker H.mulVecLin) := by omega
  rw [parityCode, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) hk

theorem solution (n d m : ℕ) (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (hZ : oddCircuitCount d M = 0) :
    ∃ v : Fin n → ZMod 2, (∀ x ∈ kerSet d M, dot v x = 1) ∧
      HasDistAtLeast (parityCode (appendRow M v)) d ∧
      2 ^ n ≤ 2 ^ (m + 1) * Nat.card (parityCode (appendRow M v)) := by
  obtain ⟨f, hf⟩ := functional_on_K n d m M hZ
  obtain ⟨v, hv⟩ := dual_as_row n f
  have hrow : ∀ x ∈ kerSet d M, dot v x = 1 := fun x hx ↦ (hv x).trans (hf x hx)
  exact ⟨v, hrow, appended_dist n d m M v hrow, code_size n (m + 1) (appendRow M v)⟩
