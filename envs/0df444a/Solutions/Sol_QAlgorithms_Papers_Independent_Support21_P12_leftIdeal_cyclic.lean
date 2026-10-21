-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P12.leftIdeal_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:59:04.201912+00:00
-- url     : https://prove2.me/submissions/73708778-c0de-44dc-9fdb-16915c3079af

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12
noncomputable section

open scoped BigOperators

def g66n2_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (W : Submodule S A) :
    Subalgebra S A where
  carrier := {a | ∀ w ∈ W, a * w ∈ W}
  mul_mem' := by
    intro a b ha hb w hw
    rw [mul_assoc]; exact ha _ (hb w hw)
  add_mem' := by
    intro a b ha hb w hw
    rw [add_mul]; exact W.add_mem (ha w hw) (hb w hw)
  algebraMap_mem' := by
    intro c w hw
    rw [← Algebra.smul_def]; exact W.smul_mem c hw

theorem g66n2_stab_iff {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (W : Submodule S A)
    (a : A) : a ∈ g66n2_stab W ↔ ∀ w ∈ W, a * w ∈ W := Iff.rfl

theorem g66n2_stab_span {S A ι : Type*} [CommRing S] [Ring A] [Algebra S A] (f : ι → A) (a : A)
    (h : ∀ j, a * f j ∈ Submodule.span S (Set.range f)) :
    a ∈ g66n2_stab (Submodule.span S (Set.range f)) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [mul_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem g66n2_free {S A X : Type*} [CommRing S] [Ring A] [Algebra S A]
    (φ : FreeAlgebra S X →ₐ[S] A) (hφ : Function.Surjective φ) (T : Subalgebra S A)
    (h : ∀ x, φ (FreeAlgebra.ι S x) ∈ T) (a : A) : a ∈ T := by
  obtain ⟨f, rfl⟩ := hφ a
  induction f using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact T.algebraMap_mem c
  | grade1 x => exact h x
  | mul a b ha hb => rw [map_mul]; exact T.mul_mem ha hb
  | add a b ha hb => rw [map_add]; exact T.add_mem ha hb

/-- the cyclotomic polynomial gives y ∈ stab -/
theorem g66n2_aeval {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (u : Fin r → S)
    (y : A) (hP : (List.ofFn fun j : Fin r => y - algebraMap S A (u j)).prod = 0) :
    Polynomial.aeval y (QAlgorithms.Papers.Independent.Support21.P12.rootPolynomial u) = 0 := by
  unfold QAlgorithms.Papers.Independent.Support21.P12.rootPolynomial
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  simpa [Function.comp_def] using hP

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_y_mem {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (u : Fin r → S)
    (y e : A) (hP : (List.ofFn fun j : Fin r => y - algebraMap S A (u j)).prod = 0) :
    y ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · have : Subsingleton A := Module.subsingleton S A
    intro w _; rw [Subsingleton.elim (y * w) 0]; exact Submodule.zero_mem _
  apply g66n2_stab_span
  intro j
  by_cases hj : j.val + 1 < r
  · have : y * cyclicFamily (S := S) y e r j = cyclicFamily (S := S) y e r ⟨j.val+1, hj⟩ := by
      simp only [cyclicFamily, ← mul_assoc, pow_succ']
    rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
  · have hjr : j.val + 1 = r := by omega
    have h0 := g66n2_aeval u y hP
    have hm : (rootPolynomial (S := S) u).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))
    have hd : (rootPolynomial (S := S) u).natDegree = r := by
      unfold rootPolynomial
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))]
      simp
    rw [hm.as_sum, hd] at h0
    simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C] at h0
    have : y * cyclicFamily (S := S) y e r j =
        -∑ i : Fin r, (rootPolynomial (S := S) u).coeff i • cyclicFamily (S := S) y e r i := by
      simp only [cyclicFamily, ← mul_assoc, ← pow_succ', hjr]
      rw [eq_neg_iff_add_eq_zero, Fin.sum_univ_eq_sum_range
        (fun i => (rootPolynomial (S := S) u).coeff i • (y ^ i * e)) r]
      simp only [Algebra.smul_def, ← mul_assoc, ← Finset.sum_mul]
      rw [← add_mul, h0, zero_mul]
    rw [this]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_e_mem {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y e : A) : e ∈ Submodule.span S (Set.range (cyclicFamily (S := S) y e r)) :=
  Submodule.subset_span ⟨⟨0, hr⟩, by simp [cyclicFamily]⟩

theorem g66n2_mul_mem {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {W : Submodule S A}
    {a w : A} (ha : a ∈ g66n2_stab W) (hw : w ∈ W) : a * w ∈ W := ha w hw

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_final {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y e : A)
    (hall : ∀ a, a ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r)))) :
    leftIdealSpan (S := S) e = Submodule.span S (Set.range (cyclicFamily (S := S) y e r)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hall a e (g66n2_e_mem hr y e)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨y ^ j.val, rfl⟩

theorem g66n2_x2pow {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (x1 x2 e : A)
    (h2 : x2 * e = -(x1 * e)) (h3 : x1 * x2 = x2 * x1) (m : ℕ) :
    x2 * (x1 ^ m * e) = -(x1 ^ (m+1) * e) := by
  have hc : Commute x2 (x1 ^ m) := (Commute.pow_right (h3.symm) m)
  rw [← mul_assoc, hc.eq, mul_assoc, h2, mul_neg, ← mul_assoc, pow_succ]

theorem g66n2_skein {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (omega : ℕ → S)
    (x1 x2 s e : A)
    (h1 : s * x1 = x2 * s + e - 1) (h2 : x2 * e = -(x1 * e)) (h3 : x1 * x2 = x2 * x1)
    (h4 : s * e = e) (h5 : ∀ a, e * x1 ^ a * e = omega a • e) :
    ∀ a : ℕ, s * x1 ^ a * e = (-1 : S) ^ a • (x1 ^ a * e) +
      (∑ k ∈ Finset.range a, ((-1 : S) ^ k * omega (a - 1 - k)) • (x1 ^ k * e)) -
      (if Odd a then x1 ^ (a - 1) * e else 0) := by
  intro a
  induction a with
  | zero => simp [h4]
  | succ a ih =>
    have step : s * x1 ^ (a+1) * e = x2 * (s * x1 ^ a * e) + omega a • e - x1 ^ a * e := by
      rw [pow_succ', ← mul_assoc s, h1, ← h5 a]; noncomm_ring
    rw [step, ih, mul_sub, mul_add, mul_smul_comm, g66n2_x2pow (S := S) x1 x2 e h2 h3, Finset.mul_sum]
    simp only [mul_smul_comm, g66n2_x2pow (S := S) x1 x2 e h2 h3]
    rw [Finset.sum_range_succ' _ a]
    have hs : ∀ k ∈ Finset.range a, ((-1 : S) ^ (k+1) * omega (a + 1 - 1 - (k+1))) • (x1 ^ (k+1) * e)
        = ((-1 : S) ^ k * omega (a - 1 - k)) • -(x1 ^ (k + 1) * e) := by
      intro k hk
      rw [show a + 1 - 1 - (k+1) = a - 1 - k by omega, pow_succ, smul_neg, mul_comm _ (-1 : S),
        mul_assoc, neg_one_mul, neg_smul]
    rw [Finset.sum_congr rfl hs]
    simp only [Nat.add_sub_cancel, pow_zero, one_mul, Nat.sub_zero, Nat.odd_add_one]
    rcases Nat.even_or_odd a with he | ho
    · have hno : ¬ Odd a := Nat.not_odd_iff_even.mpr he
      simp only [hno, if_false, not_false_eq_true, if_true, mul_zero, sub_zero, pow_succ, mul_neg,
        mul_one, neg_smul, smul_neg]
      abel
    · have hno : ¬ ¬ Odd a := not_not.mpr ho
      have ha1 : a - 1 + 1 = a := by obtain ⟨m, rfl⟩ := ho; omega
      simp only [ho, hno, if_true, if_false, not_true_eq_false]
      rw [g66n2_x2pow (S := S) x1 x2 e h2 h3 (a-1), ha1]
      simp only [pow_succ, mul_neg, mul_one, neg_smul, smul_neg]
      abel


open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_pow_e {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y e : A) (hy : y ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))))
    (k : ℕ) : y ^ k * e ∈ Submodule.span S (Set.range (cyclicFamily (S := S) y e r)) :=
  (Subalgebra.pow_mem _ hy k) e (g66n2_e_mem hr y e)

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_e_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (omega : ℕ → S) (y e : A) (h5 : ∀ a, e * y ^ a * e = omega a • e) :
    e ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))) := by
  apply g66n2_stab_span
  intro j
  simp only [cyclicFamily, ← mul_assoc, h5]
  exact Submodule.smul_mem _ _ (g66n2_e_mem hr y e)

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_x2_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y x2 e : A) (hy : y ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))))
    (h2 : x2 * e = -(y * e)) (h3 : y * x2 = x2 * y) :
    x2 ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))) := by
  apply g66n2_stab_span
  intro j
  simp only [cyclicFamily]
  rw [g66n2_x2pow (S := S) y x2 e h2 h3]
  exact Submodule.neg_mem _ (g66n2_pow_e hr y e hy _)

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_s_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (omega : ℕ → S) (y x2 s e : A)
    (hy : y ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))))
    (h1 : s * y = x2 * s + e - 1) (h2 : x2 * e = -(y * e)) (h3 : y * x2 = x2 * y)
    (h4 : s * e = e) (h5 : ∀ a, e * y ^ a * e = omega a • e) :
    s ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))) := by
  apply g66n2_stab_span
  intro j
  simp only [cyclicFamily]
  rw [← mul_assoc, g66n2_skein omega y x2 s e h1 h2 h3 h4 h5 j.val]
  have hp := g66n2_pow_e hr y e hy
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hp _))
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hp _))) ?_
  split_ifs
  · exact hp _
  · exact Submodule.zero_mem _

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_yi_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (u : Fin r → S)
    (hu : ∀ i, IsUnit (u i)) (y yi e : A)
    (hP : (List.ofFn fun j : Fin r => y - algebraMap S A (u j)).prod = 0)
    (hyi : yi * y = 1) :
    yi ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))) := by
  set W := Submodule.span S (Set.range (cyclicFamily (S := S) y e r))
  have hy := g66n2_y_mem u y e hP
  set p := rootPolynomial (S := S) u with hp
  have h0 := g66n2_aeval u y hP
  have hc : IsUnit (p.coeff 0) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hp, rootPolynomial, Polynomial.eval_prod]
    rw [IsUnit.prod_univ_iff]
    intro i; simpa using (hu i).neg
  obtain ⟨c, hc'⟩ := hc
  have hx := Polynomial.X_mul_divX_add p
  have h1 : y * Polynomial.aeval y p.divX + algebraMap S A (p.coeff 0) = 0 := by
    have := congrArg (Polynomial.aeval y) hx
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
    rw [this, h0]
  have h2 : yi = -((↑c⁻¹ : S) • Polynomial.aeval y p.divX) := by
    have := congrArg (yi * ·) h1
    simp only [mul_add, ← mul_assoc, hyi, one_mul, mul_zero] at this
    rw [← hc', ← Algebra.commutes, ← Algebra.smul_def] at this
    have h3 := congrArg (fun z => (↑c⁻¹ : S) • z) this
    simp only [smul_add, smul_smul, Units.inv_mul, one_smul, smul_zero] at h3
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
  have hq : Polynomial.aeval y p.divX ∈ g66n2_stab W :=
    (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hy)) (Polynomial.aeval_mem_adjoin_singleton S y)
  rw [h2]
  exact Subalgebra.neg_mem _ (Subalgebra.smul_mem _ hq _)

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_g_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (omega : ℕ → S) (c c1 : S) (y yi g gi e : A)
    (hy : y ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))))
    (hyis : yi ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))))
    (hyi : yi * y = 1) (hyi' : y * yi = 1) (hggi : g * gi = 1)
    (hab : y * g * y * g = g * y * g * y) (hun : g * y * g * y * e = e)
    (hsk : g - gi = algebraMap S A c * (1 - e)) (hge : g * e = algebraMap S A c1 * e)
    (h5 : ∀ a, e * y ^ a * e = omega a • e) :
    g ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))) ∧
    gi ∈ g66n2_stab (Submodule.span S (Set.range (cyclicFamily (S := S) y e r))) := by
  set W := Submodule.span S (Set.range (cyclicFamily (S := S) y e r))
  have hp := g66n2_pow_e hr y e hy
  have hes := g66n2_e_stab hr omega y e h5
  have hcomm : Commute (g * y * g) y := by
    show g * y * g * y = y * (g * y * g)
    rw [← hab]; noncomm_ring
  have hcyi : Commute yi y := by
    show yi * y = y * yi
    rw [hyi, hyi']
  have hye : g * y * g * e = yi * e := by
    calc g * y * g * e = yi * y * (g * y * g) * e := by rw [hyi, one_mul]
      _ = yi * ((g * y * g) * y * e) := by rw [mul_assoc yi y, hcomm.eq]; noncomm_ring
      _ = yi * e := by rw [hun]
  have hy' : ∀ w ∈ W, g * y * g * w = yi * w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simp only [cyclicFamily]
      rw [← mul_assoc, (hcomm.pow_right j.val).eq, mul_assoc, hye, ← mul_assoc,
        ← (hcyi.pow_right j.val).eq, mul_assoc]
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add, mul_add, hx, hz]
    | smul a x _ hx => rw [mul_smul_comm, mul_smul_comm, hx]
  have hgi_eq : gi = g - algebraMap S A c * (1 - e) := by rw [← hsk]; abel
  have key : ∀ a, g * (y ^ a * e) ∈ W := by
    intro a
    induction a with
    | zero =>
      rw [pow_zero, one_mul, hge, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (g66n2_e_mem hr y e)
    | succ a ih =>
      have h1 : gi * (y ^ a * e) ∈ W := by
        rw [hgi_eq, sub_mul, mul_assoc, ← Algebra.smul_def]
        refine Submodule.sub_mem _ ih (Submodule.smul_mem _ _ ?_)
        rw [sub_mul, one_mul]
        exact Submodule.sub_mem _ (hp a) (hes _ (hp a))
      have : g * (y ^ (a+1) * e) = g * y * g * (gi * (y ^ a * e)) := by
        rw [pow_succ']
        calc g * (y * y ^ a * e) = g * y * (g * gi) * (y ^ a * e) := by rw [hggi]; noncomm_ring
          _ = _ := by noncomm_ring
      rw [this, hy' _ h1]
      exact hyis _ h1
  have hg : g ∈ g66n2_stab W := g66n2_stab_span _ _ (fun j => key j.val)
  refine ⟨hg, ?_⟩
  rw [hgi_eq]
  exact Subalgebra.sub_mem _ hg (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
    (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hes))

open QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66n2_aff_rels (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ) (hn : 2 ≤ n) :
    affineS S omega n 0 * affineX S omega n 0 =
        affineX S omega n 1 * affineS S omega n 0 + affineE S omega n 0 - 1 ∧
    affineX S omega n 1 * affineE S omega n 0 = -(affineX S omega n 0 * affineE S omega n 0) ∧
    affineX S omega n 0 * affineX S omega n 1 = affineX S omega n 1 * affineX S omega n 0 ∧
    affineS S omega n 0 * affineE S omega n 0 = affineE S omega n 0 ∧
    affineE S omega n 0 * affineS S omega n 0 = affineE S omega n 0 ∧
    (∀ a, affineE S omega n 0 * affineX S omega n 0 ^ a * affineE S omega n 0 =
      omega a • affineE S omega n 0) := by
  have q : ∀ {x y}, BMWRel S omega n x y → affineBMWQuotientMap S omega n x =
      affineBMWQuotientMap S omega n y := fun h => RingQuot.mkAlgHom_rel S h
  have r1 := q (BMWRel.skeinLeft 0 (by omega))
  have r2 := q (BMWRel.antisymRight 0 (by omega))
  have r3 := q (BMWRel.xxCommute 0 1 (by omega) (by omega))
  have r4 := q (BMWRel.se 0 (by omega))
  have r5 := q (BMWRel.es 0 (by omega))
  have r6 := q (BMWRel.idempotent 0 (by omega))
  have r7 : ∀ a, 0 < a → _ := fun a ha => q (BMWRel.unwrap a ha hn)
  simp only [map_sub, map_mul, map_one, map_add, map_zero, map_pow, AlgHom.commutes] at r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, r3, r4, r5, ?_⟩
  · change affineS S omega n 0 * affineX S omega n 0 - affineX S omega n 1 * affineS S omega n 0 =
      affineE S omega n 0 - 1 at r1
    rw [add_sub_assoc, ← r1]; abel
  · change (affineX S omega n 0 + affineX S omega n 1) * affineE S omega n 0 = 0 at r2
    rw [add_mul] at r2
    exact eq_neg_of_add_eq_zero_right r2
  · intro a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [pow_zero, mul_one, ← pow_two, Algebra.smul_def]; exact r6
    · rw [Algebra.smul_def]; exact r7 a ha

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_h5 (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega) (a : ℕ) :
    ae S omega K 2 0 * ay S omega K 2 ^ a * ae S omega K 2 0 = omega a • ae S omega K 2 0 := by
  cases K with
  | degenerate =>
    exact (g66n2_aff_rels S omega 2 le_rfl).2.2.2.2.2 a
  | ordinary rho q hc =>
    have q' : ∀ {x y}, WRel S omega rho q 2 x y → wMap S omega rho q 2 x = wMap S omega rho q 2 y :=
      fun h => RingQuot.mkAlgHom_rel S h
    show wMap S omega rho q 2 (we S 2 0) * wMap S omega rho q 2 (wy S 2) ^ a *
      wMap S omega rho q 2 (we S 2 0) = omega a • wMap S omega rho q 2 (we S 2 0)
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have := q' (WRel.idem 0 (by omega))
      simp only [map_pow, map_mul, AlgHom.commutes] at this
      rw [pow_zero, mul_one, ← pow_two, this, Algebra.smul_def]
    · have := q' (WRel.compress a ha le_rfl)
      simp only [map_pow, map_mul, AlgHom.commutes] at this
      rw [this, Algebra.smul_def]


open QAlgorithms.Papers.Independent.Support21.P12 in
theorem g66n2_wrels (S : Type*) [CommRing S] (omega : ℕ → S) (rho q : Sˣ) :
    let m := wMap S omega rho q 2
    m (wyi S 2) * m (wy S 2) = 1 ∧ m (wy S 2) * m (wyi S 2) = 1 ∧
    m (wg S 2 0) * m (wgi S 2 0) = 1 ∧
    m (wy S 2) * m (wg S 2 0) * m (wy S 2) * m (wg S 2 0) =
      m (wg S 2 0) * m (wy S 2) * m (wg S 2 0) * m (wy S 2) ∧
    m (wg S 2 0) * m (wy S 2) * m (wg S 2 0) * m (wy S 2) * m (we S 2 0) = m (we S 2 0) ∧
    m (wg S 2 0) - m (wgi S 2 0) = algebraMap S _ ((↑q : S) - ↑(q⁻¹)) * (1 - m (we S 2 0)) ∧
    m (wg S 2 0) * m (we S 2 0) = algebraMap S _ (↑(rho⁻¹) : S) * m (we S 2 0) := by
  intro m
  have q' : ∀ {x y}, WRel S omega rho q 2 x y → m x = m y :=
    fun h => RingQuot.mkAlgHom_rel S h
  have r1 := q' WRel.invY
  have r2 := q' WRel.yInv
  have r3 := q' (WRel.gInv 0 (by omega))
  have r4 := q' (WRel.affineBraid le_rfl)
  have r5 := q' (WRel.unwrapRight le_rfl)
  have r6 := q' (WRel.skein 0 (by omega))
  have r7 := q' (WRel.ge 0 (by omega))
  simp only [map_sub, map_mul, map_one, AlgHom.commutes] at r1 r2 r3 r4 r5 r6 r7
  exact ⟨r1, r2, r3, r4, r5, by rw [map_sub]; exact r6, r7⟩

open QAlgorithms.Papers.Independent.Support21.P12 in
theorem solution (S : Type*) [CommRing S] (omega : ℕ → S)
    (K : Kind S omega) (r : ℕ) (u : Fin r → S) (hu : ValidRoots K u) :
    leftIdealSpan (S := S) (ce S omega K r u 2 0) =
      Submodule.span S (Set.range (cyclicFamily (S := S)
        (cy S omega K r u 2) (ce S omega K r u 2 0) r)) := by
  obtain ⟨hr, hroots⟩ := hu
  have h5 : ∀ a, ce S omega K r u 2 0 * cy S omega K r u 2 ^ a * ce S omega K r u 2 0 =
      omega a • ce S omega K r u 2 0 := by
    intro a
    have := congrArg (toCycl S omega K r u 2) (g66n2_h5 S omega K a)
    simp only [map_mul, map_pow, map_smul] at this
    exact this
  have hP : (List.ofFn fun j : Fin r => cy S omega K r u 2 - algebraMap S _ (u j)).prod = 0 := by
    have := RingQuot.mkAlgHom_rel S
      (show cyclRel S omega K 2 r u
        (List.ofFn fun i : Fin r => ay S omega K 2 - algebraMap S _ (u i)).prod 0 from ⟨rfl, rfl⟩)
    rw [map_zero, map_list_prod, List.map_ofFn] at this
    simp only [Function.comp_def, map_sub, AlgHom.commutes] at this
    exact this
  have hy := g66n2_y_mem u _ (ce S omega K r u 2 0) hP
  have he := g66n2_e_stab hr omega _ _ h5
  apply g66n2_final hr
  cases K with
  | degenerate =>
    obtain ⟨h1, h2, h3, h4, -, -⟩ := g66n2_aff_rels S omega 2 le_rfl
    let T : QAlgorithms.Papers.Independent.Renew46.P16.AffineBMW S omega 2 →ₐ[S]
      Cyclotomic S omega .degenerate r u 2 := toCycl S omega .degenerate r u 2
    have h1' := congrArg T h1
    have h2' := congrArg T h2
    have h3' := congrArg T h3
    have h4' := congrArg T h4
    simp only [map_mul, map_add, map_sub, map_one, map_neg] at h1' h2' h3' h4'
    have hs := g66n2_s_stab hr omega (cy S omega .degenerate r u 2) _ (cg S omega .degenerate r u 2 0)
      (ce S omega .degenerate r u 2 0) hy h1' h2' h3' h4' h5
    have hx2 := g66n2_x2_stab hr (cy S omega .degenerate r u 2) _ (ce S omega .degenerate r u 2 0)
      hy h2' h3'
    intro a
    refine g66n2_free ((toCycl S omega .degenerate r u 2).comp
      (QAlgorithms.Papers.Independent.Renew46.P16.affineBMWQuotientMap S omega 2))
      ((RingQuot.mkAlgHom_surjective _ _).comp (RingQuot.mkAlgHom_surjective _ _)) _ ?_ a
    intro x
    cases x with
    | s i =>
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
      subst hi
      exact hs
    | e i =>
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
      subst hi
      exact he
    | x i =>
      match i with
      | ⟨0, _⟩ => exact hy
      | ⟨1, _⟩ => exact hx2
  | ordinary rho q hc =>
    obtain ⟨h1, h2, h3, h4, h6, h7, h8⟩ := g66n2_wrels S omega rho q
    let T : WAffine S omega rho q 2 →ₐ[S]
      Cyclotomic S omega (.ordinary rho q hc) r u 2 := toCycl S omega (.ordinary rho q hc) r u 2
    have h1' := congrArg T h1
    have h2' := congrArg T h2
    have h3' := congrArg T h3
    have h4' := congrArg T h4
    have h6' := congrArg T h6
    have h7' := congrArg T h7
    have h8' := congrArg T h8
    simp only [map_mul, map_sub, map_one, AlgHom.commutes] at h1' h2' h3' h4' h6' h8'
    simp only [map_mul, map_sub T, map_one, AlgHom.commutes] at h7'
    have hyi := g66n2_yi_stab u hroots (cy S omega (.ordinary rho q hc) r u 2) _
      (ce S omega (.ordinary rho q hc) r u 2 0) hP h1'
    obtain ⟨hg, hgi⟩ := g66n2_g_stab hr omega _ _ (cy S omega (.ordinary rho q hc) r u 2) _
      (cg S omega (.ordinary rho q hc) r u 2 0) (cgi S omega (.ordinary rho q hc) r u 2 0)
      (ce S omega (.ordinary rho q hc) r u 2 0) hy hyi h1' h2' h3' h4' h6' h7' h8' h5
    intro a
    refine g66n2_free ((toCycl S omega (.ordinary rho q hc) r u 2).comp (wMap S omega rho q 2))
      ((RingQuot.mkAlgHom_surjective _ _).comp (RingQuot.mkAlgHom_surjective _ _)) _ ?_ a
    intro x
    cases x with
    | g i =>
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
      subst hi
      exact hg
    | gi i =>
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
      subst hi
      exact hgi
    | e i =>
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
      subst hi
      exact he
    | y => exact hy
    | yi => exact hyi
