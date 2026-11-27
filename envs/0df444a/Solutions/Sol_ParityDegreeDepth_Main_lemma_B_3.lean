-- Prove2me | solution 1 for ParityDegreeDepth.Main.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:23:42.232607+00:00
-- url     : https://prove2.me/submissions/d1a159d8-5c05-43ff-9fe3-f2405461b1e5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

open MvPolynomial
open scoped BigOperators

/-- multiplicity of a root (least total degree of a monomial of `p(a + z)`) -/
noncomputable def rootMult {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → K)
    (p : MvPolynomial (Fin n) K) : ℕ :=
  sInf ((fun s : Fin n →₀ ℕ => ∑ i, s i) '' ↑(aeval (fun i => X i + C (a i)) p).support)

namespace GridSZ
section
variable {K : Type*} [CommRing K] {n : ℕ}

noncomputable def shift (a : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun j => X j + C (a j)

lemma shift_add (a b : Fin n → K) (p : MvPolynomial (Fin n) K) :
    shift a (shift b p) = shift (a + b) p := by
  have h : (shift a).comp (shift b) = shift (a + b) := by
    ext j
    simp [shift, add_assoc]
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) h

lemma shift_zero (p : MvPolynomial (Fin n) K) : shift 0 p = p := by
  have h : shift (0 : Fin n → K) = AlgHom.id K (MvPolynomial (Fin n) K) := by
    ext j
    simp [shift]
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) h

lemma shift_ne_zero (a : Fin n → K) {p : MvPolynomial (Fin n) K} (hp : p ≠ 0) :
    shift a p ≠ 0 := by
  intro h
  have hh := congrArg (shift (-a)) h
  rw [shift_add, neg_add_cancel, shift_zero, map_zero] at hh
  exact hp hh

lemma rootMult_le (a : Fin n → K) (p : MvPolynomial (Fin n) K)
    (s : Fin n →₀ ℕ) (hs : coeff s (shift a p) ≠ 0) : rootMult a p ≤ ∑ j, s j := by
  apply Nat.sInf_le
  exact ⟨s, mem_support_iff.mpr hs, rfl⟩

lemma exists_rootMult (a : Fin n → K) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    ∃ s : Fin n →₀ ℕ, coeff s (shift a p) ≠ 0 ∧ (∑ j, s j) = rootMult a p := by
  have hs : (shift a p).support.Nonempty := by
    change (MvPolynomial.support (shift a p)).Nonempty
    exact MvPolynomial.support_nonempty.mpr (shift_ne_zero a hp)
  have hn : (((fun s : Fin n →₀ ℕ => ∑ j, s j) '' ↑(shift a p).support) : Set ℕ).Nonempty := by
    obtain ⟨s, hs⟩ := hs
    exact ⟨_, s, hs, rfl⟩
  obtain ⟨s, hs, he⟩ := Nat.sInf_mem hn
  exact ⟨s, mem_support_iff.mp hs, he⟩

noncomputable def splitR (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin n) (Polynomial K) :=
  (renameEquiv K (_root_.finSuccEquiv n)).trans (optionEquivRight K (Fin n))

lemma splitR_C (c : K) : splitR n (C c) = C (Polynomial.C c) := by
  simp [splitR, optionEquivRight_C]

lemma splitR_X_zero : splitR n (X 0 : MvPolynomial (Fin (n+1)) K) = C Polynomial.X := by
  simp [splitR, optionEquivRight_X_none]

lemma splitR_X_succ (j : Fin n) : splitR n (X j.succ : MvPolynomial (Fin (n+1)) K) = X j := by
  simp [splitR, optionEquivRight_X_some]

lemma splitR_apply (p : MvPolynomial (Fin (n+1)) K) :
    splitR n p = aeval (Fin.cases (C Polynomial.X) (fun j => X j)) p := by
  have h : (splitR (K := K) n).toAlgHom =
      aeval (Fin.cases (C Polynomial.X) (fun j => X j)) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [splitR_X_zero]
    · simp [splitR_X_succ]
  exact congrArg (fun f : MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin n) (Polynomial K) => f p) h

lemma splitR_monomial (t : Fin (n+1) →₀ ℕ) (c : K) :
    splitR n (monomial t c) = monomial t.tail (Polynomial.monomial (t 0) c) := by
  classical
  rw [splitR_apply, aeval_monomial, Finsupp.prod_pow, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [monomial_eq, Finsupp.prod_pow]
  simp only [Finsupp.tail_apply]
  rw [← map_pow]
  rw [show algebraMap K (MvPolynomial (Fin n) (Polynomial K)) c = C (Polynomial.C c) from rfl,
    ← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

lemma splitR_coeff (s : Fin n →₀ ℕ) (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    (coeff s (splitR n p)).coeff k = coeff (s.cons k) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [map_add, coeff_add, Polynomial.coeff_add, hp, hr]
  | monomial t c =>
    rw [splitR_monomial, coeff_monomial]
    by_cases ht : t.tail = s
    · rw [if_pos ht, Polynomial.coeff_monomial, coeff_monomial]
      have he : t = s.cons k ↔ t 0 = k := by
        constructor
        · intro he; simpa using congrArg (fun z => z 0) he
        · intro hk
          rw [← Finsupp.cons_tail t, ht, hk]
      simp [he]
    · rw [if_neg ht, Polynomial.coeff_zero, coeff_monomial]
      have he : t ≠ s.cons k := by intro h; apply ht; rw [h]; simp
      simp [he]


lemma splitR_shift (a : Fin n → K) (b : K)
    (p : MvPolynomial (Fin (n+1)) K) :
    splitR n (shift (Fin.cons b a) p) =
      MvPolynomial.map (Polynomial.compRingHom (Polynomial.X + Polynomial.C b))
        (shift (fun j => Polynomial.C (a j)) (splitR n p)) := by
  let f := Polynomial.compRingHom (Polynomial.X + Polynomial.C b)
  have h : (splitR (K := K) n).toRingHom.comp (shift (Fin.cons b a)).toRingHom =
      (MvPolynomial.map f).comp
        ((shift (fun j => Polynomial.C (a j))).toRingHom.comp (splitR (K := K) n).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shift, splitR_C, f, Polynomial.coe_compRingHom]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [shift, splitR_X_zero, splitR_C, f, Polynomial.coe_compRingHom]
      · simp [shift, splitR_X_succ, splitR_C, f, Polynomial.coe_compRingHom]
  exact congrArg (fun h : MvPolynomial (Fin (n+1)) K →+* MvPolynomial (Fin n) (Polynomial K) => h p) h

lemma splitL_shift (a : Fin n → K) (p : MvPolynomial (Fin (n+1)) K) :
    finSuccEquiv K n (shift (Fin.cons 0 a) p) =
      Polynomial.map (shift a).toRingHom (finSuccEquiv K n p) := by
  have h : (finSuccEquiv K n).toRingHom.comp (shift (Fin.cons 0 a)).toRingHom =
      (Polynomial.mapRingHom (shift a).toRingHom).comp (finSuccEquiv K n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [shift, finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [shift, finSuccEquiv_X_zero, finSuccEquiv_apply]
      · simp [shift, finSuccEquiv_X_succ, finSuccEquiv_apply]
  exact congrArg (fun h : MvPolynomial (Fin (n+1)) K →+* Polynomial (MvPolynomial (Fin n) K) => h p) h

lemma slice_coeff (a : Fin n → K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).coeff k =
      coeff s (shift a ((finSuccEquiv K n p).coeff k)) := by
  have hr := splitR_shift a 0 p
  have hid : Polynomial.compRingHom (Polynomial.X : Polynomial K) = RingHom.id _ :=
    RingHom.ext fun _ => Polynomial.comp_X
  simp only [Polynomial.C_0, add_zero, hid, MvPolynomial.map_id] at hr
  rw [← hr, splitR_coeff, ← finSuccEquiv_coeff_coeff s (shift (Fin.cons 0 a) p) k,
    splitL_shift, Polynomial.coeff_map]
  rfl

lemma slice_shift_coeff (a : Fin n → K) (b : K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) (k : ℕ) :
    coeff (s.cons k) (shift (Fin.cons b a) p) =
      ((coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).comp
        (Polynomial.X + Polynomial.C b)).coeff k := by
  rw [← splitR_coeff, splitR_shift, coeff_map]
  rfl

lemma univariate_sum [IsDomain K] (S : Finset K) (p : Polynomial K) :
    ∑ a ∈ S, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  have h1 : ∑ a ∈ S, p.rootMultiplicity a = ∑ a ∈ S, (p.roots.filter (· ∈ S)).count a := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Multiset.count_filter_of_pos ha, Polynomial.count_roots]
  have h2 : ∑ a ∈ S, (p.roots.filter (· ∈ S)).count a = Multiset.card (p.roots.filter (· ∈ S)) := by
    rw [← Multiset.toFinset_sum_count_eq]
    symm
    apply Finset.sum_subset
    · intro a ha
      rw [Multiset.mem_toFinset, Multiset.mem_filter] at ha
      exact ha.2
    · intro a _ ha
      rw [Multiset.mem_toFinset] at ha
      exact Multiset.count_eq_zero.mpr ha
  rw [h1, h2]
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (Polynomial.card_roots' p)

lemma slice_degree (a : Fin n → K) (s : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin (n+1)) K) :
    (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).natDegree ≤
      (finSuccEquiv K n p).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [slice_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hk, map_zero, coeff_zero]

lemma slice_root_bound [IsDomain K] (a : Fin n → K) (p : MvPolynomial (Fin (n+1)) K)
    (s : Fin n →₀ ℕ)
    (hs : coeff s (shift a (finSuccEquiv K n p).leadingCoeff) ≠ 0)
    (hm : (∑ j, s j) = rootMult a (finSuccEquiv K n p).leadingCoeff) (b : K) :
    rootMult (Fin.cons b a) p ≤ rootMult a (finSuccEquiv K n p).leadingCoeff +
      (coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))).rootMultiplicity b := by
  let r := coeff s (shift (fun j => Polynomial.C (a j)) (splitR n p))
  have hr : r ≠ 0 := by
    intro he
    have hz := congrArg (fun t : Polynomial K => t.coeff (finSuccEquiv K n p).natDegree) he
    rw [Polynomial.coeff_zero] at hz
    exact hs (by simpa only [r, slice_coeff, Polynomial.leadingCoeff] using hz)
  have hcoef : (r.comp (Polynomial.X + Polynomial.C b)).coeff (r.rootMultiplicity b) ≠ 0 := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr (Polynomial.comp_X_add_C_ne_zero_iff.mpr hr)
  have hb := rootMult_le (Fin.cons b a) p (s.cons (r.rootMultiplicity b)) (by
    rw [slice_shift_coeff]; exact hcoef)
  have hd : (∑ j, s.cons (r.rootMultiplicity b) j) = r.rootMultiplicity b + ∑ j, s j := by
    rw [Fin.sum_univ_succ]
    simp
  rw [hd, hm] at hb
  exact hb.trans_eq (add_comm _ _)

lemma sum_slices [IsDomain K] (S : Finset K)
    (p : MvPolynomial (Fin (n+1)) K) (hp : p ≠ 0) (a : Fin n → K) :
    ∑ b ∈ S, rootMult (Fin.cons b a) p ≤
      S.card * rootMult a (finSuccEquiv K n p).leadingCoeff + (finSuccEquiv K n p).natDegree := by
  have hP : finSuccEquiv K n p ≠ 0 := (finSuccEquiv K n).map_ne_zero_iff.mpr hp
  have hg : (finSuccEquiv K n p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  obtain ⟨s, hs, hm⟩ := exists_rootMult a _ hg
  have h := Finset.sum_le_sum (fun b (_ : b ∈ S) =>
    slice_root_bound a p s hs hm b)
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at h
  exact h.trans (Nat.add_le_add_left ((univariate_sum S _).trans (slice_degree a s p)) _)

/-- the DKSS multiplicity grid inequality on `S^n` -/
lemma grid_sum_bound [IsDomain K] (S : Finset K) (n : ℕ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    (∑ a : Fin n → S, rootMult (fun i => (a i : K)) p) * S.card ≤ p.totalDegree * S.card ^ n := by
  classical
  induction n with
  | zero =>
    have hm (a : Fin 0 → K) : rootMult a p = 0 := by
      obtain ⟨s, _, hs⟩ := exists_rootMult a p hp
      simpa using hs.symm
    simp only [hm, Finset.sum_const_zero, zero_mul]
    exact Nat.zero_le _
  | succ n ih =>
    let P := finSuccEquiv K n p
    have hP : P ≠ 0 := (finSuccEquiv K n).map_ne_zero_iff.mpr hp
    let g := P.leadingCoeff
    have hg : g ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hdeg : g.totalDegree + P.natDegree ≤ p.totalDegree :=
      totalDegree_coeff_finSuccEquiv_add_le p P.natDegree hg
    have hrec := ih g hg
    have hs : ∑ a : Fin (n+1) → S, rootMult (fun i => (a i : K)) p =
        ∑ a : Fin n → S, ∑ b ∈ S, rootMult (Fin.cons b (fun i => (a i : K))) p := by
      have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => S))
        (fun z => rootMult (Fin.cons (z.1 : K) (fun i => (z.2 i : K))) p)
        (fun a => rootMult (fun i => (a i : K)) p) (fun z => by
          congr 1; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.consEquiv])
      rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (Finset.sum_coe_sort S (fun b => rootMult (Fin.cons b (fun i => (a i : K))) p))
    have hsum : ∑ a : Fin (n+1) → S, rootMult (fun i => (a i : K)) p ≤
        S.card * (∑ a : Fin n → S, rootMult (fun i => (a i : K)) g) + P.natDegree * S.card ^ n := by
      rw [hs]
      have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n → S))) =>
        sum_slices S p hp (fun i => (a i : K)))
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, smul_eq_mul,
        mul_comm] using h
    have hscaled := Nat.mul_le_mul_right S.card hsum
    have hi := Nat.mul_le_mul_left S.card hrec
    have hd := Nat.mul_le_mul_right (S.card ^ (n+1)) hdeg
    rw [pow_succ] at hd ⊢
    nlinarith

end
end GridSZ

namespace ParityDegreeDepth.Main


private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def multiplicity {F : Type} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (a : Vec n F) : ℕ∞ :=
  ⨅ e ∈ (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) P).support,
    (KakeyaHasse.order e : ℕ∞)



end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- lemma B 3; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {F : Type} [Field F] {n D : ℕ} (P : MvPolynomial (Fin n) F)
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D) (S : Finset F) :
    (∑ a : Fin n → S, ParityDegreeDepth.Main.multiplicity P (fun i => (a i : F))) ≤
      ((D * S.card ^ (n - 1) : ℕ) : ℕ∞) := by
  classical
  have hshift : ∀ a : Fin n → F, (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) P).support.Nonempty := by
    intro a
    exact MvPolynomial.support_nonempty.mpr (GridSZ.shift_ne_zero a hP)
  have hmult : ∀ a : Fin n → F, ParityDegreeDepth.Main.multiplicity P a = ((rootMult a P : ℕ) : ℕ∞) := by
    intro a
    unfold ParityDegreeDepth.Main.multiplicity rootMult
    set s := (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) P).support
    have hord : ∀ e : Fin n →₀ ℕ, KakeyaHasse.order e = ∑ i, e i := by
      intro e; unfold KakeyaHasse.order; rw [Finsupp.sum_fintype]; simp
    have hne : ((fun s : Fin n →₀ ℕ => ∑ i, s i) '' (s : Set (Fin n →₀ ℕ))).Nonempty := by
      obtain ⟨e, he⟩ := hshift a; exact ⟨_, e, he, rfl⟩
    apply le_antisymm
    · obtain ⟨e, he, hle⟩ := Nat.sInf_mem hne
      calc (⨅ e ∈ s, (KakeyaHasse.order e : ℕ∞)) ≤ (KakeyaHasse.order e : ℕ∞) := iInf₂_le e he
        _ = _ := by rw [hord]; exact_mod_cast hle
    · refine le_iInf₂ fun e he => ?_
      rw [hord]
      have : sInf ((fun s : Fin n →₀ ℕ => ∑ i, s i) '' (s : Set (Fin n →₀ ℕ))) ≤ ∑ i, e i :=
        Nat.sInf_le ⟨e, he, rfl⟩
      exact_mod_cast this
  simp only [hmult]
  rw [← Nat.cast_sum]
  apply Nat.cast_le.mpr
  have hgrid := GridSZ.grid_sum_bound S n P hP
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : ∀ a : Fin 0 → S, rootMult (fun i => (a i : F)) P = 0 := by
      intro a
      obtain ⟨s, _, hs⟩ := GridSZ.exists_rootMult (fun i => (a i : F)) P hP
      simpa using hs.symm
    simp [this]
  rcases Nat.eq_zero_or_pos S.card with hS | hS
  · have : IsEmpty (Fin n → S) := by
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact ⟨fun f => Finset.notMem_empty _ (f ⟨0, hn⟩).2⟩
    simp
  · have h1 : (∑ a : Fin n → S, rootMult (fun i => (a i : F)) P) * S.card ≤
        D * S.card ^ (n - 1) * S.card := by
      calc _ ≤ P.totalDegree * S.card ^ n := hgrid
        _ ≤ D * S.card ^ n := Nat.mul_le_mul_right _ hD
        _ = D * S.card ^ (n - 1) * S.card := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
    exact Nat.le_of_mul_le_mul_right h1 hS



