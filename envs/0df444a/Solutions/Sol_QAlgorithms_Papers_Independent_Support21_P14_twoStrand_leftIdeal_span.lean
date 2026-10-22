-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P14.twoStrand_leftIdeal_span
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:23:37.975113+00:00
-- url     : https://prove2.me/submissions/f31f0638-f9f7-4c36-8fd4-526f74ed78bf

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14
noncomputable section

open scoped BigOperators Classical

def g71g4_rootPoly {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) : Polynomial S :=
  ∏ i, (Polynomial.X - Polynomial.C (u i))

def g71g4_fam {S A : Type*} [CommRing S] [Ring A] [Algebra S A]
    (y e : A) (d : ℕ) : Fin d → A := fun j => y ^ j.val * e

open scoped BigOperators

def g71g4_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (W : Submodule S A) :
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

theorem g71g4_stab_iff {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (W : Submodule S A)
    (a : A) : a ∈ g71g4_stab W ↔ ∀ w ∈ W, a * w ∈ W := Iff.rfl

theorem g71g4_stab_span {S A ι : Type*} [CommRing S] [Ring A] [Algebra S A] (f : ι → A) (a : A)
    (h : ∀ j, a * f j ∈ Submodule.span S (Set.range f)) :
    a ∈ g71g4_stab (Submodule.span S (Set.range f)) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [mul_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem g71g4_free {S A X : Type*} [CommRing S] [Ring A] [Algebra S A]
    (φ : FreeAlgebra S X →ₐ[S] A) (hφ : Function.Surjective φ) (T : Subalgebra S A)
    (h : ∀ x, φ (FreeAlgebra.ι S x) ∈ T) (a : A) : a ∈ T := by
  obtain ⟨f, rfl⟩ := hφ a
  induction f using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact T.algebraMap_mem c
  | grade1 x => exact h x
  | mul a b ha hb => rw [map_mul]; exact T.mul_mem ha hb
  | add a b ha hb => rw [map_add]; exact T.add_mem ha hb

/-- the cyclotomic polynomial gives y ∈ stab -/
theorem g71g4_aeval {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (u : Fin r → S)
    (y : A) (hP : (List.ofFn fun j : Fin r => y - algebraMap S A (u j)).prod = 0) :
    Polynomial.aeval y (g71g4_rootPoly u) = 0 := by
  unfold g71g4_rootPoly
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  simpa [Function.comp_def] using hP

theorem g71g4_y_mem {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (u : Fin r → S)
    (y e : A) (hP : (List.ofFn fun j : Fin r => y - algebraMap S A (u j)).prod = 0) :
    y ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · have : Subsingleton A := Module.subsingleton S A
    intro w _; rw [Subsingleton.elim (y * w) 0]; exact Submodule.zero_mem _
  apply g71g4_stab_span
  intro j
  by_cases hj : j.val + 1 < r
  · have : y * g71g4_fam (S := S) y e r j = g71g4_fam (S := S) y e r ⟨j.val+1, hj⟩ := by
      simp only [g71g4_fam, ← mul_assoc, pow_succ']
    rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
  · have hjr : j.val + 1 = r := by omega
    have h0 := g71g4_aeval u y hP
    have hm : (g71g4_rootPoly u).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))
    have hd : (g71g4_rootPoly u).natDegree = r := by
      unfold g71g4_rootPoly
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))]
      simp
    rw [hm.as_sum, hd] at h0
    simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C] at h0
    have : y * g71g4_fam (S := S) y e r j =
        -∑ i : Fin r, (g71g4_rootPoly u).coeff i • g71g4_fam (S := S) y e r i := by
      simp only [g71g4_fam, ← mul_assoc, ← pow_succ', hjr]
      rw [eq_neg_iff_add_eq_zero, Fin.sum_univ_eq_sum_range
        (fun i => (g71g4_rootPoly u).coeff i • (y ^ i * e)) r]
      simp only [Algebra.smul_def, ← mul_assoc, ← Finset.sum_mul]
      rw [← add_mul, h0, zero_mul]
    rw [this]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem g71g4_e_mem {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y e : A) : e ∈ Submodule.span S (Set.range (g71g4_fam (S := S) y e r)) :=
  Submodule.subset_span ⟨⟨0, hr⟩, by simp [g71g4_fam]⟩

theorem g71g4_mul_mem {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {W : Submodule S A}
    {a w : A} (ha : a ∈ g71g4_stab W) (hw : w ∈ W) : a * w ∈ W := ha w hw

theorem g71g4_final {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y e : A)
    (hall : ∀ a, a ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r)))) :
    Submodule.span S {z : A | ∃ a : A, z = a * e} = Submodule.span S (Set.range (g71g4_fam (S := S) y e r)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hall a e (g71g4_e_mem hr y e)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨y ^ j.val, rfl⟩

theorem g71g4_x2pow {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (x1 x2 e : A)
    (h2 : x2 * e = -(x1 * e)) (h3 : x1 * x2 = x2 * x1) (m : ℕ) :
    x2 * (x1 ^ m * e) = -(x1 ^ (m+1) * e) := by
  have hc : Commute x2 (x1 ^ m) := (Commute.pow_right (h3.symm) m)
  rw [← mul_assoc, hc.eq, mul_assoc, h2, mul_neg, ← mul_assoc, pow_succ]

theorem g71g4_skein {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (omega : ℕ → S)
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
    rw [step, ih, mul_sub, mul_add, mul_smul_comm, g71g4_x2pow (S := S) x1 x2 e h2 h3, Finset.mul_sum]
    simp only [mul_smul_comm, g71g4_x2pow (S := S) x1 x2 e h2 h3]
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
      rw [g71g4_x2pow (S := S) x1 x2 e h2 h3 (a-1), ha1]
      simp only [pow_succ, mul_neg, mul_one, neg_smul, smul_neg]
      abel


theorem g71g4_pow_e {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y e : A) (hy : y ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))))
    (k : ℕ) : y ^ k * e ∈ Submodule.span S (Set.range (g71g4_fam (S := S) y e r)) :=
  (Subalgebra.pow_mem _ hy k) e (g71g4_e_mem hr y e)

theorem g71g4_e_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (omega : ℕ → S) (y e : A) (h5 : ∀ a, e * y ^ a * e = omega a • e) :
    e ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))) := by
  apply g71g4_stab_span
  intro j
  simp only [g71g4_fam, ← mul_assoc, h5]
  exact Submodule.smul_mem _ _ (g71g4_e_mem hr y e)

theorem g71g4_x2_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (y x2 e : A) (hy : y ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))))
    (h2 : x2 * e = -(y * e)) (h3 : y * x2 = x2 * y) :
    x2 ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))) := by
  apply g71g4_stab_span
  intro j
  simp only [g71g4_fam]
  rw [g71g4_x2pow (S := S) y x2 e h2 h3]
  exact Submodule.neg_mem _ (g71g4_pow_e hr y e hy _)

theorem g71g4_s_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (omega : ℕ → S) (y x2 s e : A)
    (hy : y ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))))
    (h1 : s * y = x2 * s + e - 1) (h2 : x2 * e = -(y * e)) (h3 : y * x2 = x2 * y)
    (h4 : s * e = e) (h5 : ∀ a, e * y ^ a * e = omega a • e) :
    s ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))) := by
  apply g71g4_stab_span
  intro j
  simp only [g71g4_fam]
  rw [← mul_assoc, g71g4_skein omega y x2 s e h1 h2 h3 h4 h5 j.val]
  have hp := g71g4_pow_e hr y e hy
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hp _))
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hp _))) ?_
  split_ifs
  · exact hp _
  · exact Submodule.zero_mem _

theorem g71g4_yi_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (u : Fin r → S)
    (hu : ∀ i, IsUnit (u i)) (y yi e : A)
    (hP : (List.ofFn fun j : Fin r => y - algebraMap S A (u j)).prod = 0)
    (hyi : yi * y = 1) :
    yi ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))) := by
  set W := Submodule.span S (Set.range (g71g4_fam (S := S) y e r))
  have hy := g71g4_y_mem u y e hP
  set p := g71g4_rootPoly u with hp
  have h0 := g71g4_aeval u y hP
  have hc : IsUnit (p.coeff 0) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hp, g71g4_rootPoly, Polynomial.eval_prod]
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
  have hq : Polynomial.aeval y p.divX ∈ g71g4_stab W :=
    (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hy)) (Polynomial.aeval_mem_adjoin_singleton S y)
  rw [h2]
  exact Subalgebra.neg_mem _ (Subalgebra.smul_mem _ hq _)

theorem g71g4_g_stab {S A : Type*} [CommRing S] [Ring A] [Algebra S A] {r : ℕ} (hr : 0 < r)
    (omega : ℕ → S) (c c1 : S) (y yi g gi e : A)
    (hy : y ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))))
    (hyis : yi ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))))
    (hyi : yi * y = 1) (hyi' : y * yi = 1) (hggi : g * gi = 1)
    (hab : y * g * y * g = g * y * g * y) (hun : g * y * g * y * e = e)
    (hsk : g - gi = algebraMap S A c * (1 - e)) (hge : g * e = algebraMap S A c1 * e)
    (h5 : ∀ a, e * y ^ a * e = omega a • e) :
    g ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))) ∧
    gi ∈ g71g4_stab (Submodule.span S (Set.range (g71g4_fam (S := S) y e r))) := by
  set W := Submodule.span S (Set.range (g71g4_fam (S := S) y e r))
  have hp := g71g4_pow_e hr y e hy
  have hes := g71g4_e_stab hr omega y e h5
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
      simp only [g71g4_fam]
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
      exact Submodule.smul_mem _ _ (g71g4_e_mem hr y e)
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
  have hg : g ∈ g71g4_stab W := g71g4_stab_span _ _ (fun j => key j.val)
  refine ⟨hg, ?_⟩
  rw [hgi_eq]
  exact Subalgebra.sub_mem _ hg (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
    (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hes))


open QAlgorithms.Papers.Independent.Support21.P14

theorem g71g4_rels {S : Type*} [CommRing S] {r : ℕ} (P : GroundParameters S r) :
    bmwY P 2 true * bmwY P 2 false = 1 ∧ bmwY P 2 false * bmwY P 2 true = 1 ∧
    bmwG P 2 0 false * bmwG P 2 0 true = 1 ∧
    bmwY P 2 false * bmwG P 2 0 false * bmwY P 2 false * bmwG P 2 0 false =
      bmwG P 2 0 false * bmwY P 2 false * bmwG P 2 0 false * bmwY P 2 false ∧
    bmwY P 2 false * bmwG P 2 0 false * bmwY P 2 false * bmwE P 2 0 =
      algebraMap S _ (P.rho : S) * bmwE P 2 0 ∧
    bmwG P 2 0 false - bmwG P 2 0 true =
      algebraMap S _ ((↑P.q : S) - ↑P.q⁻¹) * (1 - bmwE P 2 0) ∧
    bmwG P 2 0 false * bmwE P 2 0 = algebraMap S _ (↑P.rho⁻¹ : S) * bmwE P 2 0 ∧
    (List.ofFn fun j : Fin r => bmwY P 2 false - algebraMap S _ (P.u j : S)).prod = 0 ∧
    (∀ a, bmwE P 2 0 * bmwY P 2 false ^ a * bmwE P 2 0 = P.delta a • bmwE P 2 0) := by
  have q' : ∀ {x y}, MultiplicativeBMWRel P 2 x y → bmwMap P 2 x = bmwMap P 2 y :=
    fun h => RingQuot.mkAlgHom_rel S h
  have r1 := q' (.braid (.yInvR (by omega)))
  have r2 := q' (.braid (.yInvL (by omega)))
  have r3 := q' (.braid (.gInvL 0 (by omega)))
  have r4 := q' (.braid (.affine le_rfl))
  have r5 := q' (.unwrapR le_rfl)
  have r6 := q' (.skein 0 (by omega))
  have r7 := q' (.untwistL 0 (by omega))
  have r8 := q' (.braid (.cyclotomic (by omega)))
  have r9 := q' (.idempotent 0 (by omega))
  have r10 : ∀ j, 1 ≤ j → _ := fun j hj => q' (.delta j hj le_rfl)
  simp only [map_sub, map_mul, map_one, map_zero, map_pow, AlgHom.commutes, map_list_prod,
    List.map_ofFn, Function.comp_def] at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  refine ⟨r1, r2, r3, r4, r5, ?_, r7, r8, ?_⟩
  · rw [map_sub]; exact r6
  · intro a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [pow_zero, mul_one, ← pow_two, Algebra.smul_def]; exact r9
    · rw [Algebra.smul_def]; exact r10 a ha

theorem solution {S : Type*} [CommRing S] {r : ℕ}
    (P : GroundParameters S r) :
    Submodule.span S {z : BMW P 2 | ∃ a : BMW P 2, z = a * bmwE P 2 0} =
      Submodule.span S (Set.range (twoStrandFamily P)) := by
  have hr := P.positive
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hP, hd⟩ := g71g4_rels P
  have hfam : twoStrandFamily P = g71g4_fam (S := S) (bmwY P 2 false) (bmwE P 2 0) r := rfl
  rw [hfam]
  have hun : bmwG P 2 0 false * bmwY P 2 false * bmwG P 2 0 false * bmwY P 2 false * bmwE P 2 0 =
      bmwE P 2 0 := by
    calc _ = bmwG P 2 0 false * (bmwY P 2 false * bmwG P 2 0 false * bmwY P 2 false * bmwE P 2 0) := by
            noncomm_ring
      _ = _ := by
        rw [h5, ← mul_assoc, ← Algebra.commutes, mul_assoc, h7, ← mul_assoc, ← map_mul,
          Units.mul_inv, map_one, one_mul]
  have hy := g71g4_y_mem (fun j => (P.u j : S)) _ (bmwE P 2 0) hP
  have he := g71g4_e_stab hr P.delta _ _ hd
  have hyi := g71g4_yi_stab (fun j => (P.u j : S)) (fun j => (P.u j).isUnit) (bmwY P 2 false) _
    (bmwE P 2 0) hP h1
  obtain ⟨hg, hgi⟩ := g71g4_g_stab hr P.delta _ _ (bmwY P 2 false) _
    (bmwG P 2 0 false) (bmwG P 2 0 true) (bmwE P 2 0) hy hyi h1 h2 h3 h4 hun h6 h7 hd
  apply g71g4_final hr
  intro a
  refine g71g4_free (bmwMap P 2) (RingQuot.mkAlgHom_surjective _ _) _ ?_ a
  intro x
  cases x with
  | g i b =>
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
    subst hi
    cases b
    · exact hg
    · exact hgi
  | e i =>
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
    subst hi
    exact he
  | y i b =>
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
    subst hi
    cases b
    · exact hy
    · exact hyi
