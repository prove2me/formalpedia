-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P12.minimal_split_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:05:07.433877+00:00
-- url     : https://prove2.me/submissions/dd94158d-ff17-4adb-9dc1-adccbc28d6ae

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section
open scoped BigOperators
open Polynomial

namespace QAlgorithms.Papers.Independent.Support21.P12

lemma X7C18_cycl (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega) (r : ℕ) (u : Fin r → S) :
    Polynomial.aeval (cy S omega K r u 2) (rootPolynomial u) = 0 := by
  have hroot : rootPolynomial u = (List.ofFn fun i : Fin r => (Polynomial.X - Polynomial.C (u i))).prod := by
    rw [List.prod_ofFn]; rfl
  have h1 : Polynomial.aeval (cy S omega K r u 2) (rootPolynomial u) =
      toCycl S omega K r u 2 (Polynomial.aeval (ay S omega K 2) (rootPolynomial u)) := by
    unfold cy
    rw [Polynomial.aeval_algHom_apply]
  rw [h1, hroot, map_list_prod, List.map_ofFn]
  have h2 : ((fun p => Polynomial.aeval (ay S omega K 2) p) ∘ fun i : Fin r => Polynomial.X - Polynomial.C (u i)) =
      fun i : Fin r => ay S omega K 2 - algebraMap S _ (u i) := by
    funext i; simp [Polynomial.aeval_X, Polynomial.aeval_C]
  rw [h2]
  have hr : cyclRel S omega K 2 r u
      (List.ofFn fun i : Fin r => ay S omega K 2 - algebraMap S _ (u i)).prod 0 := ⟨rfl, rfl⟩
  have := RingQuot.mkAlgHom_rel S hr
  rw [map_zero] at this
  exact this

section general

variable {S A : Type*} [CommRing S] [Ring A] [Algebra S A]

lemma X7C18_indep {y e : A} {d : ℕ} (hli : LinearIndependent S (cyclicFamily (S := S) y e d))
    (f : S[X]) (hf : f ≠ 0) (hdeg : f.natDegree < d) : Polynomial.aeval y f * e ≠ 0 := by
  intro h0
  apply hf
  rw [Polynomial.aeval_eq_sum_range' hdeg, Finset.sum_mul, Finset.sum_range] at h0
  have h1 : ∑ j : Fin d, f.coeff j • cyclicFamily (S := S) y e d j = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [cyclicFamily, smul_mul_assoc]
  have h2 := Fintype.linearIndependent_iff.mp hli (fun j => f.coeff j) h1
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n < d
  · exact h2 ⟨n, hn⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma X7C18_dep {y e : A} {d : ℕ} (hnli : ¬ LinearIndependent S (cyclicFamily (S := S) y e (d+1))) :
    ∃ f : S[X], f ≠ 0 ∧ f.natDegree ≤ d ∧ Polynomial.aeval y f * e = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg, i, hi⟩ := hnli
  refine ⟨∑ j : Fin (d+1), Polynomial.monomial (j : ℕ) (g j), ?_, ?_, ?_⟩
  · intro h
    apply hi
    have := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj
      rw [if_neg]
      intro h'; exact hj (Fin.ext h')
    · simp
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  · rw [map_sum, Finset.sum_mul, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.aeval_monomial, cyclicFamily, Algebra.smul_def, mul_assoc]

end general

lemma X7C18_lift {α β : Type*} [DecidableEq α] [DecidableEq β] (u : α → β) :
    ∀ (t : Multiset α) (s : Multiset β), s ≤ t.map u → ∃ t' ≤ t, t'.map u = s := by
  intro t
  induction t using Multiset.induction_on with
  | empty =>
    intro s hs
    refine ⟨0, le_refl _, ?_⟩
    simp only [Multiset.map_zero] at hs
    simpa using (le_zero_iff.mp hs).symm
  | cons a t ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases ha : u a ∈ s
    · have h1 : s.erase (u a) ≤ t.map u := by
        rw [← Multiset.cons_erase ha] at hs
        exact (Multiset.cons_le_cons_iff _).mp hs
      obtain ⟨t', ht', hm⟩ := ih _ h1
      refine ⟨a ::ₘ t', Multiset.cons_le_cons _ ht', ?_⟩
      rw [Multiset.map_cons, hm, Multiset.cons_erase ha]
    · have h1 : s ≤ t.map u := (Multiset.le_cons_of_notMem ha).mp hs
      obtain ⟨t', ht', hm⟩ := ih _ h1
      exact ⟨t', ht'.trans (Multiset.le_cons_self _ _), hm⟩

lemma X7C18_rootPoly_eq {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) :
    rootPolynomial u = ((Finset.univ.val.map u).map fun a => X - C a).prod := by
  rw [rootPolynomial, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

lemma X7C18_rootPoly_monic {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) :
    (rootPolynomial u).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (u i)

lemma X7C18_rootPoly_deg {S : Type*} [CommRing S] [Nontrivial S] {r : ℕ} (u : Fin r → S) :
    (rootPolynomial u).natDegree = r := by
  rw [rootPolynomial, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (u i)]
  simp

/-- key algebraic step: a nonzero annihilating polynomial of degree d divides a scalar multiple
of the root polynomial. -/
lemma X7C18_dvd {S : Type*} [CommRing S] [IsDomain S] {A : Type*} [Ring A] [Algebra S A]
    {y e : A} {d : ℕ} (hd : 0 < d) (hli : LinearIndependent S (cyclicFamily (S := S) y e d))
    (P f : S[X]) (hP : Polynomial.aeval y P * e = 0) (hf : Polynomial.aeval y f * e = 0)
    (hfd : f.natDegree = d) :
    ∃ D : S, D ≠ 0 ∧ ∃ q : S[X], C D * P = f * q := by
  classical
  let Kf := FractionRing S
  let P' : Kf[X] := P.map (algebraMap S Kf)
  let f' : Kf[X] := f.map (algebraMap S Kf)
  have hinj : Function.Injective (algebraMap S Kf) := IsFractionRing.injective S Kf
  have hf'd : f'.natDegree = d := by
    simp only [f']; rw [Polynomial.natDegree_map_eq_of_injective hinj, hfd]
  obtain ⟨⟨b, hb⟩, hbq⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors S) (P' / f')
  set q0 := IsLocalization.integerNormalization (nonZeroDivisors S) (P' / f') with hq0
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b, hb0, q0, ?_⟩
  set rem := C b * P - f * q0 with hrem
  have hremI : Polynomial.aeval y rem * e = 0 := by
    have hc : Polynomial.aeval y (f * q0) = Polynomial.aeval y q0 * Polynomial.aeval y f := by
      rw [mul_comm, map_mul]
    rw [hrem, map_sub, sub_mul, hc, map_mul, Polynomial.aeval_C, mul_assoc, hP, mul_zero,
      mul_assoc, hf, mul_zero, sub_zero]
  have hmap : rem.map (algebraMap S Kf) = b • (P' % f') := by
    rw [hrem, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, hbq]
    rw [Algebra.smul_def, Algebra.smul_def, Polynomial.algebraMap_apply,
      EuclideanDomain.mod_eq_sub_mul_div]
    simp only [P', f']
    ring
  by_contra hne
  have hrem0 : rem ≠ 0 := by
    intro h; apply hne; rw [hrem, sub_eq_zero] at h; exact h
  apply X7C18_indep hli rem hrem0 _ hremI
  have hmod0 : P' % f' ≠ 0 := by
    intro h; apply hrem0
    have : rem.map (algebraMap S Kf) = 0 := by rw [hmap, h, smul_zero]
    exact (Polynomial.map_eq_zero_iff hinj).mp this
  have h1 : rem.natDegree = (rem.map (algebraMap S Kf)).natDegree :=
    (Polynomial.natDegree_map_eq_of_injective hinj _).symm
  rw [h1, hmap]
  refine (Polynomial.natDegree_smul_le _ _).trans_lt ?_
  rw [← hf'd]
  exact Polynomial.natDegree_mod_lt _ (by omega)

end QAlgorithms.Papers.Independent.Support21.P12

end

open QAlgorithms.Papers.Independent.Support21.P12 Polynomial in
theorem solution (S : Type*) [CommRing S] [IsDomain S]
    (omega : ℕ → S) (K : Kind S omega) (r : ℕ) (u : Fin r → S)
    (hu : ValidRoots K u) (htor : IdealTorsionFree S omega K r u)
    (d : ℕ) (hsemi : SemiAdmissible S omega K r u d) :
    ∃ sigma : Equiv.Perm (Fin r), ∃ h : d ≤ r,
      let v : Fin d → S := fun i => u (sigma ⟨i.val, lt_of_lt_of_le i.isLt h⟩)
      Polynomial.aeval (cy S omega K r u 2) (rootPolynomial v) * ce S omega K r u 2 0 = 0 ∧
      (rootPolynomial v).Monic ∧ (rootPolynomial v).natDegree = d ∧
      (∀ f : Polynomial S, f ≠ 0 → f.natDegree < d →
        Polynomial.aeval (cy S omega K r u 2) f * ce S omega K r u 2 0 ≠ 0) := by
  classical
  obtain ⟨hd0, hdr, hli, hnli⟩ := hsemi
  obtain ⟨f, hf0, hfle, hfI⟩ := X7C18_dep hnli
  have hfd : f.natDegree = d := by
    by_contra h; exact X7C18_indep hli f hf0 (by omega) hfI
  have hP : Polynomial.aeval (cy S omega K r u 2) (rootPolynomial u) * ce S omega K r u 2 0 = 0 := by
    rw [X7C18_cycl, zero_mul]
  obtain ⟨D, hD, q, hq⟩ := X7C18_dvd hd0 hli _ f hP hfI hfd
  have hPne : C D * rootPolynomial u ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hD) (X7C18_rootPoly_monic u).ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hPne hq
  have hfq : f * q ≠ 0 := mul_ne_zero hf0 hq0
  have hroots : (C D * rootPolynomial u).roots = Finset.univ.val.map u := by
    rw [Polynomial.roots_C_mul _ hD, X7C18_rootPoly_eq, Polynomial.roots_multiset_prod_X_sub_C]
  have hdegP : (C D * rootPolynomial u).natDegree = r := by
    rw [Polynomial.natDegree_C_mul hD, X7C18_rootPoly_deg]
  have hcardP : Multiset.card (C D * rootPolynomial u).roots = r := by rw [hroots]; simp
  rw [hq] at hroots hdegP hcardP
  rw [Polynomial.roots_mul hfq] at hcardP hroots
  rw [Polynomial.natDegree_mul hf0 hq0] at hdegP
  have h1 := Polynomial.card_roots' f
  have h2 := Polynomial.card_roots' q
  rw [Multiset.card_add] at hcardP
  have hcf : Multiset.card f.roots = f.natDegree := by omega
  have hle : f.roots ≤ Finset.univ.val.map u := hroots ▸ Multiset.le_add_right _ _
  obtain ⟨t', ht', hmap⟩ := X7C18_lift u _ _ hle
  have hnd : t'.Nodup := Multiset.nodup_of_le ht' Finset.univ.nodup
  let T : Finset (Fin r) := ⟨t', hnd⟩
  have hTcard : T.card = d := by
    show Multiset.card t' = d
    rw [← Multiset.card_map u, hmap, hcf, hfd]
  let eT : Fin d ≃ T := (T.equivFinOfCardEq hTcard).symm
  let e0 : {x : Fin r // x.val < d} ≃ Fin d :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.2 hdr.le⟩, i.2⟩
      left_inv := fun x => rfl
      right_inv := fun i => rfl }
  let e1 : {x : Fin r // x.val < d} ≃ {x // x ∈ T} := e0.trans eT
  refine ⟨Equiv.extendSubtype e1, hdr.le, ?_⟩
  intro v
  have hv : ∀ i : Fin d, v i = u (eT i) := by
    intro i
    show u (Equiv.extendSubtype e1 ⟨i.val, _⟩) = _
    rw [Equiv.extendSubtype_apply_of_mem e1 _ (show i.val < d from i.2)]
    rfl
  have hprod : rootPolynomial v = (f.roots.map fun a => X - C a).prod := by
    rw [rootPolynomial]
    simp only [hv]
    rw [Equiv.prod_comp eT (fun t : T => X - C (u t)), Finset.prod_coe_sort T (fun t => X - C (u t)),
      Finset.prod_eq_multiset_prod, ← hmap, Multiset.map_map]
    rfl
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcf
  refine ⟨?_, X7C18_rootPoly_monic v, ?_, fun g hg hgd => X7C18_indep hli g hg hgd⟩
  · rw [hprod]
    set m := (f.roots.map fun a => X - C a).prod
    apply htor f.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hf0)
    · exact Submodule.subset_span ⟨Polynomial.aeval (cy S omega K r u 2) m, rfl⟩
    · rw [Algebra.smul_def, ← mul_assoc, ← Polynomial.aeval_C (cy S omega K r u 2), ← map_mul, hfac]
      exact hfI
  · rw [X7C18_rootPoly_deg]
