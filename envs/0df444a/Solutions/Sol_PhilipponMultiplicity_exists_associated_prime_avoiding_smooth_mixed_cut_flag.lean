-- Prove2me | solution 1 for PhilipponMultiplicity.exists_associated_prime_avoiding_smooth_mixed_cut_flag
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-04T20:09:57.425211+00:00
-- url     : https://prove2.me/submissions/28830202-07d8-4254-a1d1-1efa00c60167
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_principal_open_smooth_mixed_flag_family
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.GenericChoice
variable {K σ : Type*} [Field K] [Infinite K]

theorem exists_eval_ne_zero (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 := by
  by_contra! h
  apply hF
  apply MvPolynomial.funext
  intro x
  simpa using h x

/-- A nonempty principal open in affine space meets the complement of any
finite union of proper linear subspaces. -/
theorem exists_eval_ne_zero_avoiding_subspaces [Fintype σ]
    (S : Finset (Submodule K (σ → K))) (hS : ∀ U ∈ S, U ≠ ⊤)
    (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 ∧ ∀ U ∈ S, x ∉ U := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    obtain ⟨x,hx⟩ := exists_eval_ne_zero F hF
    exact ⟨x,hx,by simp⟩
  | @insert U S hUS ih =>
    have hU : U ≠ ⊤ := hS U (Finset.mem_insert_self _ _)
    obtain ⟨v,hv⟩ : ∃ v : σ → K, v ∉ U := by
      by_contra! h
      exact hU (top_unique (fun x _ => h x))
    obtain ⟨f,hfv,hUf⟩ := Submodule.exists_le_ker_of_notMem hv
    let g : MvPolynomial σ K := ∑ i, MvPolynomial.C (f (Pi.single i 1)) * MvPolynomial.X i
    have heval (x : σ → K) : MvPolynomial.eval x g = f x := by
      calc
        MvPolynomial.eval x g = ∑ i, f (Pi.single i 1) * x i := by simp [g]
        _ = f (∑ i, x i • Pi.single i (1 : K)) := by
          simp [map_sum, map_smul, smul_eq_mul, mul_comm]
        _ = f x := by
          congr 1
          ext j
          simp [Pi.single_apply]
    have hg : g ≠ 0 := by
      intro hz
      have := heval v
      rw [hz, map_zero] at this
      exact hfv this.symm
    obtain ⟨x,hx,havoid⟩ := ih (fun V hV => hS V (Finset.mem_insert_of_mem hV))
      (F * g) (mul_ne_zero hF hg)
    rw [map_mul, mul_ne_zero_iff] at hx
    refine ⟨x,hx.1,?_⟩
    intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · intro hxU
      apply hx.2
      rw [heval]
      exact hUf hxU
    · exact havoid V hV

/-- A finite sequence of choices can be made inside any principal open,
provided each next-row condition is dense and only depends on its prefix. -/
theorem exists_sequential_choice
    (n : ℕ) (Good : Fin n → (Fin n → σ → K) → Prop)
    (hprefix : ∀ i c d, (∀ j : Fin n, j.val ≤ i.val → c j = d j) →
      (Good i c ↔ Good i d))
    (hdense : ∀ (i : Fin n) (c : Fin n → σ → K) (F : MvPolynomial σ K),
      F ≠ 0 → ∃ a : σ → K, MvPolynomial.eval a F ≠ 0 ∧
        Good i (Function.update c i a))
    (F : MvPolynomial (Fin n × σ) K) (hF : F ≠ 0) :
    ∃ c : Fin n → σ → K, MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
      ∀ i, Good i c := by
  classical
  have haux : ∀ k : ℕ, k ≤ n →
      ∃ c : Fin n → σ → K, MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
        ∀ i : Fin n, i.val < k → Good i c := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨x,hx⟩ := exists_eval_ne_zero F hF
      exact ⟨Function.curry x, by simpa using hx, by simp⟩
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      let i : Fin n := ⟨k,hk⟩
      obtain ⟨c,hc,hgood⟩ := ih (by omega)
      let G : MvPolynomial σ K := MvPolynomial.bind₁
        (fun w : Fin n × σ => if w.1 = i then MvPolynomial.X w.2
          else MvPolynomial.C (c w.1 w.2)) F
      have heval (a : σ → K) :
          MvPolynomial.eval a G =
            MvPolynomial.eval (Function.uncurry (Function.update c i a)) F := by
        change MvPolynomial.eval₂Hom (RingHom.id K) a
          (MvPolynomial.bind₁ _ F) = _
        rw [MvPolynomial.eval₂Hom_bind₁]
        apply congrArg (fun y : Fin n × σ → K => MvPolynomial.eval y F)
        funext w
        by_cases hw : w.1 = i
        · simp [hw, Function.uncurry]
        · simp [hw, Function.uncurry, Function.update_of_ne hw]
      have hG : G ≠ 0 := by
        intro hz
        have hh := heval (c i)
        rw [hz, map_zero, Function.update_eq_self] at hh
        exact hc hh.symm
      obtain ⟨a,ha,hnew⟩ := hdense i c G hG
      refine ⟨Function.update c i a, (heval a).symm ▸ ha, ?_⟩
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hnew
      · have hjk : j.val < k := by
          have hne : j.val ≠ k := fun h => hji (Fin.ext h)
          omega
        apply (hprefix j c (Function.update c i a) ?_).mp (hgood j hjk)
        intro t ht
        have hti : t ≠ i := by
          intro hti
          have : t.val = k := congrArg Fin.val hti
          omega
        exact (Function.update_of_ne hti _ _).symm
  obtain ⟨c,hc,hgood⟩ := haux n le_rfl
  exact ⟨c,hc,fun i => hgood i i.isLt⟩

end PhilipponMultiplicity.GenericChoice

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem rowForm_single (i : M.FactorIndex) (j : Fin (M.ambientDimension i + 1)) :
    rowForm M i (Pi.single ⟨i,j⟩ 1) = MvPolynomial.X ⟨i,j⟩ := by
  classical
  simp [rowForm, Pi.single_apply]

theorem rowForm_homogeneous (b : M.FactorIndex) (a : M.Variable → K) :
    M.IsHomogeneous (rowForm M b a) (Pi.single b 1) := by
  classical
  intro m hm i
  change m ∈ (∑ t : Fin (M.ambientDimension b + 1),
    a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)).support at hm
  have hs := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun t : Fin (M.ambientDimension b + 1) =>
      a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)) hm
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hs
  have hmX : m ∈ (MvPolynomial.X (⟨b,t⟩ : M.Variable) : M.CoordinateRing).support :=
    MvPolynomial.support_smul ht
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hmX
  subst m
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b,t⟩ : M.Variable) ≠ ⟨i,k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, Pi.single_apply, hi, hn]

theorem polynomial_homogeneous (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) :
    M.IsHomogeneous (polynomial M l c j) (Pi.single l[j] 1) :=
  rowForm_homogeneous M l[j] (c j)

theorem ideal_zero (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) : ideal M I l c 0 = I := by
  simp [ideal]

theorem ideal_prefix (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c d : Fin l.length → M.Variable → K) (k : ℕ)
    (h : ∀ j : Fin l.length, j.val < k → c j = d j) :
    ideal M I l c k = ideal M I l d k := by
  classical
  unfold ideal
  congr 1
  apply iSup_congr
  intro j
  apply iSup_congr
  intro hj
  simp [polynomial, h j hj]

theorem ideal_succ (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (k : ℕ) (hk : k < l.length) :
    ideal M I l c (k+1) = ideal M I l c k ⊔
      Ideal.span {polynomial M l c ⟨k,hk⟩} := by
  unfold ideal
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_sup_left) ?_
    refine iSup_le fun j => iSup_le fun hj => ?_
    by_cases hjk : j.val < k
    · exact le_sup_of_le_left (le_sup_of_le_right
        (le_iSup_of_le j (le_iSup_of_le hjk le_rfl)))
    · have he : j = ⟨k,hk⟩ := Fin.ext (by change j.val = k; omega)
      subst j
      exact le_sup_right
  · refine sup_le (sup_le le_sup_left ?_) ?_
    · refine iSup_le fun j => iSup_le fun hj => ?_
      exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le (by omega : j.val < k+1) le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le ⟨k,hk⟩ (le_iSup_of_le (by simp) le_rfl))

/-- Associated-prime avoidance in any nonempty principal open of one block's
coefficient space. No geometric hypotheses on the initial ideal are needed. -/
theorem exists_row_avoiding_associatedPrimes [Infinite K]
    (I : Ideal M.CoordinateRing) (i : M.FactorIndex)
    (F : MvPolynomial M.Variable K) (hF : F ≠ 0) :
    ∃ a : M.Variable → K, MvPolynomial.eval a F ≠ 0 ∧
      ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ I) (M.CoordinateRing ⧸ I),
        (∀ b : M.FactorIndex, ∃ j : Fin (M.ambientDimension b + 1),
          Ideal.Quotient.mk I (MvPolynomial.X ⟨b,j⟩) ∉ q) →
        Ideal.Quotient.mk I (rowForm M i a) ∉ q := by
  classical
  let Q := M.CoordinateRing ⧸ I
  let φ : (M.Variable → K) →ₗ[K] Q :=
    (Ideal.Quotient.mkₐ K I).toLinearMap.comp (rowForm M i)
  let bad (q : Ideal Q) : Submodule K (M.Variable → K) :=
    (q.restrictScalars K).comap φ
  let S := (associatedPrimes.finite Q Q).toFinset.filter
    (fun q => ∀ b : M.FactorIndex, ∃ j : Fin (M.ambientDimension b + 1),
      Ideal.Quotient.mk I (MvPolynomial.X ⟨b,j⟩) ∉ q)
  have hproper : ∀ U ∈ S.image bad, U ≠ ⊤ := by
    intro U hU
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hq).2 i
    intro he
    have hv : Pi.single (⟨i,j⟩ : M.Variable) (1 : K) ∈ bad q := by
      rw [he]
      trivial
    change Ideal.Quotient.mk I (rowForm M i (Pi.single ⟨i,j⟩ 1)) ∈ q at hv
    rw [rowForm_single] at hv
    exact hj hv
  obtain ⟨a,ha,havoid⟩ := GenericChoice.exists_eval_ne_zero_avoiding_subspaces
    (S.image bad) hproper F hF
  refine ⟨a,ha,?_⟩
  intro q hq hblocks
  exact havoid (bad q) (Finset.mem_image.mpr ⟨q,
    Finset.mem_filter.mpr ⟨by simpa using hq, hblocks⟩,rfl⟩)

/-- Filter-regular flags meet every nonempty principal open of coefficient matrices. -/
theorem exists_flag_avoiding_associatedPrimes [Infinite K]
    (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (F : MvPolynomial (Fin l.length × M.Variable) K) (hF : F ≠ 0) :
    ∃ c : Fin l.length → M.Variable → K,
      MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
      ∀ j : Fin l.length,
        ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ ideal M I l c j.val)
          (M.CoordinateRing ⧸ ideal M I l c j.val),
          (∀ b : M.FactorIndex, ∃ t : Fin (M.ambientDimension b + 1),
            Ideal.Quotient.mk (ideal M I l c j.val) (MvPolynomial.X ⟨b,t⟩) ∉ q) →
          Ideal.Quotient.mk (ideal M I l c j.val) (polynomial M l c j) ∉ q := by
  classical
  let Good (j : Fin l.length) (c : Fin l.length → M.Variable → K) : Prop :=
    ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ ideal M I l c j.val)
      (M.CoordinateRing ⧸ ideal M I l c j.val),
      (∀ b : M.FactorIndex, ∃ t : Fin (M.ambientDimension b + 1),
        Ideal.Quotient.mk (ideal M I l c j.val) (MvPolynomial.X ⟨b,t⟩) ∉ q) →
      Ideal.Quotient.mk (ideal M I l c j.val) (polynomial M l c j) ∉ q
  apply GenericChoice.exists_sequential_choice l.length Good ?_ ?_ F hF
  · intro j c d hp
    have hI := ideal_prefix M I l c d j.val (fun t ht => hp t (by omega))
    have hP : polynomial M l c j = polynomial M l d j := by
      simp [polynomial, hp j le_rfl]
    dsimp [Good]
    rw [hI,hP]
  · intro j c G hG
    obtain ⟨a,ha,havoid⟩ := exists_row_avoiding_associatedPrimes M
      (ideal M I l c j.val) l[j] G hG
    refine ⟨a,ha,?_⟩
    have hI : ideal M I l (Function.update c j a) j.val = ideal M I l c j.val := by
      apply ideal_prefix
      intro t ht
      exact Function.update_of_ne (fun he => by subst t; omega) _ _
    dsimp [Good]
    rw [hI]
    simpa [polynomial] using havoid

end PhilipponMultiplicity.MixedFlag

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem associated_prime_avoiding_flag_of_principal_open_family
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hchoice : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ l : List M.FactorIndex, (∀ i, l.count i = α i) ∧
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
              (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
              (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
              (∀ x : M.Point, x ∈ linearSlice M W L ↔ x ∈ W ∧
                ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0) ∧
              (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ q ∈ associatedPrimes
                (M.CoordinateRing ⧸ J k) (M.CoordinateRing ⧸ J k),
              (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                Ideal.Quotient.mk (J k) (MvPolynomial.X ⟨i,j⟩) ∉ q) →
              Ideal.Quotient.mk (J k) (P k) ∉ q) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ q : PrimeSpectrum (M.CoordinateRing ⧸ J l.length),
            (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
              Ideal.Quotient.mk (J l.length) (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
            Algebra.IsSmoothAt K q.asIdeal) := by
  classical
  intro M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨l,hcount,F,hF,hfamily⟩ := hchoice M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨c,hc,havoid⟩ := MixedFlag.exists_flag_avoiding_associatedPrimes M
    (M.vanishingIdeal W) l F hF
  obtain ⟨L,hL,hfinite,hdisjoint,hgeometry,hfinal⟩ := hfamily c hc
  let P : ℕ → M.CoordinateRing := fun k => if hk : k < l.length then
    MixedFlag.polynomial M l c ⟨k,hk⟩ else 0
  let J : ℕ → Ideal M.CoordinateRing := MixedFlag.ideal M (M.vanishingIdeal W) l c
  refine ⟨L,hL,hfinite,hdisjoint,l,P,J,hcount,
    MixedFlag.ideal_zero M (M.vanishingIdeal W) l c,?_,?_,hfinal⟩
  · intro k hk
    refine ⟨?_,?_,?_⟩
    · simpa [P,hk] using MixedFlag.polynomial_homogeneous M l c ⟨k,hk⟩
    · simpa only [P,dif_pos hk,J] using
        MixedFlag.ideal_succ M (M.vanishingIdeal W) l c k hk
    · simpa only [P,dif_pos hk,J] using havoid ⟨k,hk⟩
  · intro x
    rw [hgeometry]
    constructor
    · rintro ⟨hx,hpx⟩
      refine ⟨hx,?_⟩
      intro k hk
      simpa only [P,dif_pos hk] using hpx ⟨k,hk⟩
    · rintro ⟨hx,hpx⟩
      refine ⟨hx,?_⟩
      intro j
      simpa only [P,dif_pos j.isLt] using hpx j.val j.isLt

end PhilipponMultiplicity

end

end

set_option maxHeartbeats 1000000
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ q ∈ associatedPrimes
                (M.CoordinateRing ⧸ J k) (M.CoordinateRing ⧸ J k),
              (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                Ideal.Quotient.mk (J k) (MvPolynomial.X ⟨i,j⟩) ∉ q) →
              Ideal.Quotient.mk (J k) (P k) ∉ q) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ q : PrimeSpectrum (M.CoordinateRing ⧸ J l.length),
            (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
              Ideal.Quotient.mk (J l.length) (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
            Algebra.IsSmoothAt K q.asIdeal) := by
  exact associated_prime_avoiding_flag_of_principal_open_family K hK
    (exists_principal_open_smooth_mixed_flag_family K hK)
