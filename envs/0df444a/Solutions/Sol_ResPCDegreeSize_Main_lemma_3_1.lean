-- Prove2me | solution 1 for ResPCDegreeSize.Main.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T03:05:13.781306+00:00
-- url     : https://prove2.me/submissions/2f9338da-abbc-4c00-be11-8ea617366552

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial
open ResPCDegreeSize.Main
open Module
open Matrix

namespace ResPCLemma31

/-- The maximal ideal of the point c. -/
noncomputable def mI {F : Type} [Field F] {s : ℕ} (c : Fin s → F) : Ideal (MvPolynomial (Fin s) F) :=
  Ideal.span (Set.range fun i : Fin s => (X i - C (c i) : MvPolynomial (Fin s) F))

lemma eval_mem {F : Type} [Field F] {s : ℕ} (c : Fin s → F) (f : MvPolynomial (Fin s) F)
    (h : eval c f = 0) : f ∈ mI c := by
  have key : ∀ f : MvPolynomial (Fin s) F, f - C (eval c f) ∈ mI c := by
    intro f
    refine MvPolynomial.induction_on (motive := fun f => f - C (eval c f) ∈ mI c) f ?_ ?_ ?_
    · intro a; simp
    · intro p q hp hq
      have := add_mem hp hq
      have e : p + q - C (eval c (p + q)) = (p - C (eval c p)) + (q - C (eval c q)) := by
        rw [map_add, map_add]; ring
      rw [e]; exact this
    · intro p i hp
      have h1 := Ideal.mul_mem_right (X i) _ hp
      have h2 : C (eval c p) * (X i - C (c i)) ∈ mI c :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      have := add_mem h1 h2
      have e : p * X i - C (eval c (p * X i))
          = (p - C (eval c p)) * X i + C (eval c p) * (X i - C (c i)) := by
        rw [map_mul, eval_X, map_mul]; ring
      rw [e]; exact this
  have := key f
  rwa [h, map_zero, sub_zero] at this

/-- Coefficientwise application of a linear functional. -/
noncomputable def Lam {F : Type} [Field F] {s : ℕ} (L : MvPolynomial (Fin s) F →ₗ[F] F)
    (Q : Polynomial (MvPolynomial (Fin s) F)) : Polynomial F :=
  ∑ j ∈ Q.support, Polynomial.monomial j (L (Q.coeff j))

section LamLemmas
variable {F : Type} [Field F] {s : ℕ} (L : MvPolynomial (Fin s) F →ₗ[F] F)

lemma Lam_coeff (Q : Polynomial (MvPolynomial (Fin s) F)) (j : ℕ) :
    (Lam L Q).coeff j = L (Q.coeff j) := by
  unfold Lam
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Polynomial.notMem_support_iff.1 h, map_zero]

lemma Lam_zero : Lam L 0 = 0 := by
  ext j; rw [Lam_coeff, Polynomial.coeff_zero, map_zero, Polynomial.coeff_zero]

lemma Lam_add (Q1 Q2 : Polynomial (MvPolynomial (Fin s) F)) :
    Lam L (Q1 + Q2) = Lam L Q1 + Lam L Q2 := by
  ext j; rw [Lam_coeff, Polynomial.coeff_add, Polynomial.coeff_add, map_add, Lam_coeff, Lam_coeff]

lemma Lam_sub (Q1 Q2 : Polynomial (MvPolynomial (Fin s) F)) :
    Lam L (Q1 - Q2) = Lam L Q1 - Lam L Q2 := by
  ext j; rw [Lam_coeff, Polynomial.coeff_sub, Polynomial.coeff_sub, map_sub, Lam_coeff, Lam_coeff]

lemma Lam_X (Q : Polynomial (MvPolynomial (Fin s) F)) :
    Lam L (Polynomial.X * Q) = Polynomial.X * Lam L Q := by
  ext j
  cases j with
  | zero => rw [Lam_coeff, Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul_zero, map_zero]
  | succ j => rw [Lam_coeff, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, Lam_coeff]

lemma Lam_CC (a : F) (Q : Polynomial (MvPolynomial (Fin s) F)) :
    Lam L (Polynomial.C (C a) * Q) = Polynomial.C a * Lam L Q := by
  ext j
  rw [Lam_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Lam_coeff, MvPolynomial.C_mul',
    map_smul, smul_eq_mul]

lemma Lam_XsubC (a : F) (Q : Polynomial (MvPolynomial (Fin s) F)) :
    Lam L ((Polynomial.X - Polynomial.C (C a)) * Q) = (Polynomial.X - Polynomial.C a) * Lam L Q := by
  rw [sub_mul, Lam_sub, Lam_X, Lam_CC, sub_mul]

lemma Lam_Cmul_zero (h : MvPolynomial (Fin s) F) (hh : ∀ q, L (h * q) = 0)
    (Q : Polynomial (MvPolynomial (Fin s) F)) : Lam L (Polynomial.C h * Q) = 0 := by
  ext j; rw [Lam_coeff, Polynomial.coeff_C_mul, hh, Polynomial.coeff_zero]

/-- The filtration property used in the induction. -/
abbrev UP (I : Ideal (MvPolynomial (Fin s) F)) (m : ℕ) (a0 : F) (k : ℕ)
    (Q : Polynomial (MvPolynomial (Fin s) F)) : Prop :=
  ∀ i : ℕ, ∀ h ∈ I ^ i, (Polynomial.X - Polynomial.C a0) ^ (k + i - m) ∣ Lam L (Polynomial.C h * Q)

lemma UP_zero (I : Ideal (MvPolynomial (Fin s) F)) (m : ℕ) (a0 : F) (k : ℕ) :
    UP L I m a0 k 0 := by
  intro i h _
  rw [mul_zero, Lam_zero]; exact dvd_zero _

lemma UP_add (I : Ideal (MvPolynomial (Fin s) F)) (m : ℕ) (a0 : F) (k : ℕ)
    {Q1 Q2 : Polynomial (MvPolynomial (Fin s) F)} (h1 : UP L I m a0 k Q1) (h2 : UP L I m a0 k Q2) :
    UP L I m a0 k (Q1 + Q2) := by
  intro i h hh
  rw [mul_add, Lam_add]; exact dvd_add (h1 i h hh) (h2 i h hh)

lemma UP_mul (I : Ideal (MvPolynomial (Fin s) F)) (m : ℕ) (a0 : F) (k : ℕ)
    (u : Polynomial (MvPolynomial (Fin s) F)) {Q : Polynomial (MvPolynomial (Fin s) F)}
    (hQ : UP L I m a0 k Q) : UP L I m a0 k (u * Q) := by
  refine Polynomial.induction_on u ?_ ?_ ?_
  · intro r i h hh
    have h1 := hQ i (h * r) (Ideal.mul_mem_right r _ hh)
    have e : Polynomial.C h * (Polynomial.C r * Q) = Polynomial.C (h * r) * Q := by
      rw [Polynomial.C_mul]; ring
    rw [e]; exact h1
  · intro p q hp hq i h hh
    rw [add_mul, mul_add, Lam_add]; exact dvd_add (hp i h hh) (hq i h hh)
  · intro n r ih i h hh
    have e : Polynomial.C h * (Polynomial.C r * Polynomial.X ^ (n+1) * Q)
        = Polynomial.X * (Polynomial.C h * (Polynomial.C r * Polynomial.X ^ n * Q)) := by ring
    rw [e, Lam_X]; exact Dvd.dvd.mul_left (ih i h hh) _

lemma UP0 (I : Ideal (MvPolynomial (Fin s) F)) (m : ℕ) (a0 : F)
    (hL0 : ∀ h ∈ I ^ (m+1), L h = 0) (Q : Polynomial (MvPolynomial (Fin s) F)) :
    UP L I m a0 0 Q := by
  intro i h hh
  by_cases hi : i ≤ m
  · have e : 0 + i - m = 0 := by omega
    rw [e, pow_zero]; exact one_dvd _
  · have hz : Lam L (Polynomial.C h * Q) = 0 :=
      Lam_Cmul_zero L h (fun q => hL0 (h * q)
        (Ideal.mul_mem_right q _ (Ideal.pow_le_pow_right (by omega : m + 1 ≤ i) hh))) Q
    rw [hz]; exact dvd_zero _

noncomputable def Uid (I : Ideal (MvPolynomial (Fin s) F)) (m : ℕ) (a0 : F) (k : ℕ) :
    Ideal (Polynomial (MvPolynomial (Fin s) F)) where
  carrier := {Q | UP L I m a0 k Q}
  add_mem' := by intro Q1 Q2 h1 h2; exact UP_add L I m a0 k h1 h2
  zero_mem' := UP_zero L I m a0 k
  smul_mem' := by intro u Q hQ; exact UP_mul L I m a0 k u hQ

lemma key_dvd (c : Fin (s+1) → F) (m : ℕ)
    (hL0 : ∀ h ∈ mI (fun j : Fin s => c j.succ) ^ (m+1), L h = 0) (k : ℕ)
    (Δ : MvPolynomial (Fin (s+1)) F) (hΔ : Δ ∈ mI c ^ k) :
    (Polynomial.X - Polynomial.C (c 0)) ^ (k - m) ∣ Lam L (finSuccEquiv F s Δ) := by
  have hC : ∀ a : F, finSuccEquiv F s (C a) = Polynomial.C (C a) := fun a => by
    simp [finSuccEquiv_apply]
  let φ : MvPolynomial (Fin (s+1)) F →+* Polynomial (MvPolynomial (Fin s) F) :=
    (finSuccEquiv F s : MvPolynomial (Fin (s+1)) F →+* Polynomial (MvPolynomial (Fin s) F))
  have hφ : ∀ x, φ x = finSuccEquiv F s x := fun x => rfl
  have hJ : ∀ k : ℕ, (Ideal.span (Set.range fun i : Fin (s+1) => φ (X i - C (c i)))) ^ k
      ≤ Uid L (mI (fun j : Fin s => c j.succ)) m (c 0) k := by
    intro k
    induction k with
    | zero => intro Q _; exact UP0 L _ m (c 0) hL0 Q
    | succ k ihk =>
      rw [Submodule.pow_succ]
      refine Ideal.mul_le.2 fun q hq n hn => ?_
      have hq' : UP L (mI (fun j : Fin s => c j.succ)) m (c 0) k q := ihk hq
      refine Submodule.span_induction
        (p := fun n _ => q * n ∈ Uid L (mI (fun j : Fin s => c j.succ)) m (c 0) (k+1))
        ?_ ?_ ?_ ?_ hn
      · rintro x ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · have e : φ (X 0 - C (c 0)) = Polynomial.X - Polynomial.C (C (c 0)) := by
            rw [hφ, map_sub, finSuccEquiv_X_zero, hC]
          show q * φ (X 0 - C (c 0)) ∈ _
          rw [e]
          intro i' h hh
          have h1 := hq' i' h hh
          have e2 : Polynomial.C h * (q * (Polynomial.X - Polynomial.C (C (c 0))))
              = (Polynomial.X - Polynomial.C (C (c 0))) * (Polynomial.C h * q) := by ring
          rw [e2, Lam_XsubC]
          calc (Polynomial.X - Polynomial.C (c 0)) ^ (k + 1 + i' - m)
              ∣ (Polynomial.X - Polynomial.C (c 0)) ^ (k + i' - m + 1) :=
                pow_dvd_pow _ (by omega)
            _ = (Polynomial.X - Polynomial.C (c 0)) * (Polynomial.X - Polynomial.C (c 0)) ^ (k + i' - m) :=
                pow_succ' _ _
            _ ∣ _ := mul_dvd_mul_left _ h1
        · have e : φ (X j.succ - C (c j.succ)) = Polynomial.C (X j - C (c j.succ)) := by
            rw [hφ, map_sub, finSuccEquiv_X_succ, hC, Polynomial.C_sub]
          show q * φ (X j.succ - C (c j.succ)) ∈ _
          rw [e]
          intro i' h hh
          have hg : (X j - C (c j.succ) : MvPolynomial (Fin s) F) ∈ mI (fun j : Fin s => c j.succ) :=
            Ideal.subset_span ⟨j, rfl⟩
          have h1 := hq' (i'+1) (h * (X j - C (c j.succ)))
            (by rw [Submodule.pow_succ]; exact Ideal.mul_mem_mul hh hg)
          have e2 : Polynomial.C h * (q * Polynomial.C (X j - C (c j.succ)))
              = Polynomial.C (h * (X j - C (c j.succ))) * q := by
            rw [Polynomial.C_mul]; ring
          rw [e2]
          have e3 : k + 1 + i' - m = k + (i'+1) - m := by omega
          rw [e3]; exact h1
      · rw [mul_zero]; exact zero_mem _
      · intro x y _ _ hx hy
        rw [mul_add]; exact add_mem hx hy
      · intro a x _ hx
        rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ a hx
  have hmem : φ Δ ∈ (Ideal.span (Set.range fun i : Fin (s+1) => φ (X i - C (c i)))) ^ k := by
    have h1 : Ideal.map φ (mI c ^ k)
        = (Ideal.span (Set.range fun i : Fin (s+1) => φ (X i - C (c i)))) ^ k := by
      rw [Ideal.map_pow]
      congr 1
      unfold mI
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [← h1]; exact Ideal.mem_map_of_mem φ hΔ
  have h2 : UP L (mI (fun j : Fin s => c j.succ)) m (c 0) k (φ Δ) := hJ k hmem
  have h3 := h2 0 1 (by rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial)
  rw [map_one, one_mul, add_zero, hφ] at h3
  exact h3

end LamLemmas

theorem multSZ {F : Type} [Field F] [Fintype F] : ∀ (s : ℕ) (Δ : MvPolynomial (Fin s) F), Δ ≠ 0 →
    ∀ k : (Fin s → F) → ℕ, (∀ c, Δ ∈ mI c ^ k c) →
    Fintype.card F * ∑ c, k c ≤ Δ.totalDegree * Fintype.card F ^ s := by
  classical
  intro s
  induction s with
  | zero =>
    intro Δ hΔ k hk
    have h0 : ∀ c, k c = 0 := by
      intro c
      by_contra hne
      have h1 : Δ ∈ mI c := Ideal.pow_le_self hne (hk c)
      have h2 : mI c = ⊥ := by
        unfold mI; rw [Set.range_eq_empty, Ideal.span_empty]
      rw [h2] at h1
      exact hΔ ((Ideal.mem_bot).1 h1)
    simp [h0]
  | succ s ih =>
    intro Δ hΔ k hk
    have hP0 : finSuccEquiv F s Δ ≠ 0 := (EmbeddingLike.map_ne_zero_iff).2 hΔ
    have hlc : (finSuccEquiv F s Δ).coeff (finSuccEquiv F s Δ).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.2 hP0
    generalize htdef : (finSuccEquiv F s Δ).natDegree = t at hlc
    have hdeg : ((finSuccEquiv F s Δ).coeff t).totalDegree + t ≤ Δ.totalDegree :=
      totalDegree_coeff_finSuccEquiv_add_le Δ t hlc
    have hpos : 0 < Fintype.card F := Fintype.card_pos
    have hex : ∀ a' : Fin s → F, ∃ m, (finSuccEquiv F s Δ).coeff t ∈ mI a' ^ m ∧
        (finSuccEquiv F s Δ).coeff t ∉ mI a' ^ (m+1) := by
      intro a'
      by_contra hcon
      have hstep : ∀ m, (finSuccEquiv F s Δ).coeff t ∈ mI a' ^ m →
          (finSuccEquiv F s Δ).coeff t ∈ mI a' ^ (m+1) := by
        intro m hm
        by_contra h2
        exact hcon ⟨m, hm, h2⟩
      have hall : ∀ m, (finSuccEquiv F s Δ).coeff t ∈ mI a' ^ m := by
        intro m
        induction m with
        | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial
        | succ m ihm => exact hstep m ihm
      have hbad := ih ((finSuccEquiv F s Δ).coeff t) hlc
        (fun b => if b = a' then ((finSuccEquiv F s Δ).coeff t).totalDegree * Fintype.card F ^ s + 1
          else 0)
        (fun b => by
          by_cases hb : b = a'
          · rw [if_pos hb, hb]; exact hall _
          · rw [if_neg hb, Submodule.pow_zero, Ideal.one_eq_top]; trivial)
      rw [Finset.sum_ite_eq' Finset.univ a', if_pos (Finset.mem_univ _)] at hbad
      have := Nat.le_mul_of_pos_left
        (((finSuccEquiv F s Δ).coeff t).totalDegree * Fintype.card F ^ s + 1) hpos
      omega
    choose m hm1 hm2 using hex
    have hIH := ih ((finSuccEquiv F s Δ).coeff t) hlc m hm1
    have hkey : ∀ a' : Fin s → F,
        ∑ a0 : F, k (Fin.cons a0 a') ≤ Fintype.card F * m a' + t := by
      intro a'
      obtain ⟨L, hL1, hL2⟩ := Submodule.exists_le_ker_of_notMem (K := F)
        (p := (mI a' ^ (m a' + 1)).restrictScalars F) (v := (finSuccEquiv F s Δ).coeff t)
        (by rw [Submodule.restrictScalars_mem]; exact hm2 a')
      have hL0 : ∀ h ∈ mI a' ^ (m a' + 1), L h = 0 := fun h hh =>
        LinearMap.mem_ker.1 (hL2 ((Submodule.restrictScalars_mem F _ h).2 hh))
      have hdvd : ∀ a0 : F, (Polynomial.X - Polynomial.C a0) ^ (k (Fin.cons a0 a') - m a')
          ∣ Lam L (finSuccEquiv F s Δ) := by
        intro a0
        have h := key_dvd L (Fin.cons a0 a' : Fin (s+1) → F) (m a')
          (by simpa using hL0) (k (Fin.cons a0 a')) Δ (hk _)
        simpa using h
      have hg0 : Lam L (finSuccEquiv F s Δ) ≠ 0 := by
        intro h0
        apply hL1
        have := Lam_coeff L (finSuccEquiv F s Δ) t
        rw [h0, Polynomial.coeff_zero] at this
        exact this.symm
      have hgd : (Lam L (finSuccEquiv F s Δ)).natDegree ≤ t := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [Lam_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [htdef]; exact hN), map_zero]
      have hsum : ∑ a0 : F, (k (Fin.cons a0 a') - m a') ≤ t := by
        calc ∑ a0 : F, (k (Fin.cons a0 a') - m a')
            ≤ ∑ a0 : F, (Lam L (finSuccEquiv F s Δ)).roots.count a0 :=
              Finset.sum_le_sum fun a0 _ => by
                rw [Polynomial.count_roots]
                exact (Polynomial.le_rootMultiplicity_iff hg0).2 (hdvd a0)
          _ = Multiset.card (Lam L (finSuccEquiv F s Δ)).roots :=
              Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
          _ ≤ t := (Polynomial.card_roots' _).trans hgd
      calc ∑ a0 : F, k (Fin.cons a0 a')
          ≤ ∑ a0 : F, ((k (Fin.cons a0 a') - m a') + m a') :=
            Finset.sum_le_sum fun a0 _ => by omega
        _ = (∑ a0 : F, (k (Fin.cons a0 a') - m a')) + Fintype.card F * m a' := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        _ ≤ Fintype.card F * m a' + t := by omega
    have hsplit : ∑ c, k c = ∑ a' : Fin s → F, ∑ a0 : F, k (Fin.cons a0 a') := by
      rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (s+1) => F)
        (fun x => k (Fin.cons x.1 x.2)) k (fun x => rfl)]
      exact Fintype.sum_prod_type_right _
    have hcardfun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by simp
    have h1 : ∑ c, k c ≤ Fintype.card F * ∑ a', m a' + t * Fintype.card F ^ s := by
      rw [hsplit]
      calc ∑ a' : Fin s → F, ∑ a0 : F, k (Fin.cons a0 a')
          ≤ ∑ a' : Fin s → F, (Fintype.card F * m a' + t) :=
            Finset.sum_le_sum fun a' _ => hkey a'
        _ = Fintype.card F * ∑ a', m a' + t * Fintype.card F ^ s := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              hcardfun, smul_eq_mul, mul_comm t]
    have h2 : ∑ c, k c ≤ Δ.totalDegree * Fintype.card F ^ s := by
      calc ∑ c, k c ≤ Fintype.card F * ∑ a', m a' + t * Fintype.card F ^ s := h1
        _ ≤ ((finSuccEquiv F s Δ).coeff t).totalDegree * Fintype.card F ^ s
              + t * Fintype.card F ^ s := Nat.add_le_add_right hIH _
        _ = (((finSuccEquiv F s Δ).coeff t).totalDegree + t) * Fintype.card F ^ s := by ring
        _ ≤ Δ.totalDegree * Fintype.card F ^ s := Nat.mul_le_mul_right _ hdeg
    calc Fintype.card F * ∑ c, k c ≤ Fintype.card F * (Δ.totalDegree * Fintype.card F ^ s) :=
          Nat.mul_le_mul_left _ h2
      _ = Δ.totalDegree * Fintype.card F ^ (s+1) := by ring

/-- The generic matrix with polynomial entries. -/
noncomputable def Pm {F : Type} [Field F] {s r : ℕ} (B : Fin s → Matrix (Fin r) (Fin r) F) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin s) F) :=
  ∑ i, (X i : MvPolynomial (Fin s) F) • (B i).map (C : F →+* MvPolynomial (Fin s) F)

lemma entry_deg {F : Type} [Field F] {s r : ℕ} (B : Fin s → Matrix (Fin r) (Fin r) F)
    (i j : Fin r) : ((Pm B) i j).totalDegree ≤ 1 := by
  have h : (Pm B) i j = ∑ l, X l * C (B l i j) := by
    simp [Pm, Matrix.sum_apply]
  rw [h]
  refine totalDegree_finsetSum_le fun l _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X, totalDegree_C]

lemma det_degree {F : Type} [Field F] {s r : ℕ} (B : Fin s → Matrix (Fin r) (Fin r) F) :
    (Pm B).det.totalDegree ≤ r := by
  rw [Matrix.det_apply']
  refine totalDegree_finsetSum_le fun σ _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin s) F).totalDegree = 0 := by
    have : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin s) F)
        = C ((Equiv.Perm.sign σ : ℤ) : F) := by simp
    rw [this, totalDegree_C]
  rw [h1, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j, ((Pm B) (σ j) j).totalDegree ≤ ∑ _j : Fin r, 1 :=
        Finset.sum_le_sum fun j _ => entry_deg B _ _
    _ = r := by simp

lemma ordDet {F : Type} [Field F] {s r : ℕ} (B : Fin s → Matrix (Fin r) (Fin r) F)
    (c : Fin s → F) : (Pm B).det ∈ mI c ^ (r - (∑ i, c i • B i).rank) := by
  classical
  set Bc : Matrix (Fin r) (Fin r) F := ∑ i, c i • B i with hBc
  let K : Submodule F (Fin r → F) := LinearMap.ker Bc.mulVecLin
  obtain ⟨K', hK'⟩ := K.exists_isCompl
  let bK := Module.finBasis F K
  let bK' := Module.finBasis F K'
  let b0 := (bK.prod bK').map (Submodule.prodEquivOfIsCompl K K' hK')
  have hcard : Fintype.card (Fin (Module.finrank F K) ⊕ Fin (Module.finrank F K'))
      = Fintype.card (Fin r) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      Submodule.finrank_add_eq_of_isCompl hK', Module.finrank_fin_fun]
  let e := Fintype.equivOfCardEq hcard
  let b := b0.reindex e
  have hbK : ∀ i, Bc *ᵥ (b (e (Sum.inl i))) = 0 := by
    intro i
    have h1 : b (e (Sum.inl i)) = (bK i : Fin r → F) := by
      simp [b, b0, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    rw [h1]
    exact LinearMap.mem_ker.1 (bK i).2
  let V : Matrix (Fin r) (Fin r) F := fun i j => b j i
  have hV : IsUnit V.det := by
    have hVeq : V = (Pi.basisFun F (Fin r)).toMatrix b := by
      ext i j; simp [V, Basis.toMatrix_apply]
    haveI := (Pi.basisFun F (Fin r)).invertibleToMatrix b
    rw [hVeq]; exact Matrix.isUnit_det_of_invertible _
  let T : Finset (Fin r) := Finset.univ.image fun i : Fin (Module.finrank F K) => e (Sum.inl i)
  have hT : T.card = r - Bc.rank := by
    show (Finset.univ.image fun i : Fin (Module.finrank F K) => e (Sum.inl i)).card = _
    rw [Finset.card_image_of_injective _
      (fun i j h => Sum.inl_injective (e.injective h) :
        Function.Injective fun i : Fin (Module.finrank F K) => e (Sum.inl i)),
      Finset.card_univ, Fintype.card_fin]
    have h := LinearMap.finrank_range_add_finrank_ker Bc.mulVecLin
    rw [Module.finrank_fin_fun] at h
    have h' : Bc.rank + Module.finrank F K = r := h
    omega
  let Vc : Matrix (Fin r) (Fin r) (MvPolynomial (Fin s) F) :=
    (C : F →+* MvPolynomial (Fin s) F).mapMatrix V
  have hev : ∀ i j, eval c ((Pm B * Vc) i j) = (Bc *ᵥ (b j)) i := by
    intro i j
    simp [Pm, hBc, V, Vc, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact eval_C _
  have hentry : ∀ j ∈ T, ∀ i, (Pm B * Vc) i j ∈ mI c := by
    intro j hj i
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hj
    apply eval_mem
    rw [hev, hbK]; rfl
  have hdetA : (Pm B * Vc).det ∈ mI c ^ T.card := by
    rw [Matrix.det_apply']
    refine Ideal.sum_mem _ fun σ _ => Ideal.mul_mem_left _ _ ?_
    have h1 : ∏ j, (Pm B * Vc) (σ j) j ∈ ∏ j : Fin r, (if j ∈ T then mI c else 1) :=
      Ideal.prod_mem_prod fun j _ => by
        split_ifs with hj
        · exact hentry j hj _
        · rw [Ideal.one_eq_top]; trivial
    rwa [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const] at h1
  have hdet : (Pm B * Vc).det = (Pm B).det * C V.det := by
    rw [Matrix.det_mul]
    show (Pm B).det * ((C : F →+* MvPolynomial (Fin s) F).mapMatrix V).det = _
    rw [← RingHom.map_det]
  have hne : V.det ≠ 0 := hV.ne_zero
  have hfin : (Pm B).det = (Pm B * Vc).det * C (V.det)⁻¹ := by
    rw [hdet, mul_assoc, ← C_mul, mul_inv_cancel₀ hne, C_1, mul_one]
  rw [hfin, ← hT]
  exact Ideal.mul_mem_right _ _ hdetA

lemma exists_rows {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] (N : Matrix m n K) :
    ∃ f : Fin N.rank → m, LinearIndependent K (N.submatrix f id).row := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (K := K) N.row
  haveI : Finite κ := Finite.of_injective a ha
  haveI := Fintype.ofFinite κ
  have hc : Fintype.card κ = N.rank := by
    rw [N.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  exact ⟨a ∘ (Fintype.equivFinOfCardEq hc).symm,
    hli.comp _ (Fintype.equivFinOfCardEq hc).symm.injective⟩

lemma exists_minor {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] (N : Matrix m n K) :
    ∃ (f : Fin N.rank → m) (g : Fin N.rank → n), (N.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := exists_rows N
  obtain ⟨g', hg'⟩ := exists_rows (N.submatrix f id)ᵀ
  have hr : ((N.submatrix f id)ᵀ).rank = N.rank := by
    rw [Matrix.rank_transpose, hf.rank_matrix, Fintype.card_fin]
  have hli : LinearIndependent K
      (((N.submatrix f id)ᵀ.submatrix (g' ∘ Fin.cast hr.symm) id).row) :=
    hg'.comp _ (Fin.cast_injective _)
  have hsq : (N.submatrix f id)ᵀ.submatrix (g' ∘ Fin.cast hr.symm) id
      = (N.submatrix f (g' ∘ Fin.cast hr.symm))ᵀ := by
    ext i j; rfl
  rw [hsq] at hli
  have hunit := Matrix.linearIndependent_rows_iff_isUnit.1 hli
  refine ⟨f, g' ∘ Fin.cast hr.symm, ?_⟩
  have h := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  rw [Matrix.det_transpose] at h
  exact h.ne_zero

end ResPCLemma31

open ResPCLemma31 in
theorem solution {p s a b : ℕ} [Fact p.Prime] (M : Fin s → Matrix (Fin a) (Fin b) (ZMod p)) :
    (1 - 1 / (p : ℝ)) * ((matLam M).rank : ℝ) ≤
      (∑ c : Fin s → ZMod p, ((∑ i, c i • M i).rank : ℝ)) / (p : ℝ) ^ s := by
  classical
  obtain ⟨f, g, hdet⟩ := exists_minor (matLam M)
  generalize hrdef : (matLam M).rank = r at f g hdet ⊢
  let B : Fin s → Matrix (Fin r) (Fin r) (ZMod p) := fun i => (M i).submatrix f g
  have hsub : (matLam M).submatrix f g
      = (Pm B).map (algebraMap (MvPolynomial (Fin s) (ZMod p)) (FpLam p s)) := by
    ext i j
    simp only [Matrix.submatrix_apply, matLam, lam, Pm, B, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [IsScalarTower.algebraMap_apply (ZMod p) (MvPolynomial (Fin s) (ZMod p)) (FpLam p s),
      MvPolynomial.algebraMap_eq]
  have hΔ : (Pm B).det ≠ 0 := by
    intro h0
    apply hdet
    rw [hsub, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hdeg : (Pm B).det.totalDegree ≤ r := det_degree B
  have hord : ∀ c : Fin s → ZMod p, (Pm B).det ∈ mI c ^ (r - (∑ i, c i • M i).rank) := by
    intro c
    refine Ideal.pow_le_pow_right ?_ (ordDet B c)
    have h1 : (∑ i, c i • B i) = (∑ i, c i • M i).submatrix f g := by
      ext i j; simp [B, Matrix.sum_apply]
    rw [h1]
    have h2 := Matrix.rank_submatrix_le (∑ i, c i • M i) f g
    omega
  have hSZ := multSZ s (Pm B).det hΔ _ hord
  rw [ZMod.card] at hSZ
  have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  have hterm : ∀ c : Fin s → ZMod p, (r : ℝ) - ((∑ i, c i • M i).rank : ℝ)
      ≤ ((r - (∑ i, c i • M i).rank : ℕ) : ℝ) := by
    intro c
    have h : r ≤ (r - (∑ i, c i • M i).rank) + (∑ i, c i • M i).rank := by omega
    have h' : (r : ℝ) ≤ ((r - (∑ i, c i • M i).rank : ℕ) : ℝ) + ((∑ i, c i • M i).rank : ℝ) := by
      exact_mod_cast h
    linarith
  have hconst : ∑ _c : Fin s → ZMod p, (r : ℝ) = (p : ℝ) ^ s * r := by
    simp [ZMod.card]
  have hD : (p : ℝ) ^ s * r - ∑ c : Fin s → ZMod p, ((∑ i, c i • M i).rank : ℝ)
      ≤ ((∑ c : Fin s → ZMod p, (r - (∑ i, c i • M i).rank) : ℕ) : ℝ) := by
    rw [Nat.cast_sum, ← hconst, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun c _ => hterm c
  have hc : ((p * ∑ c : Fin s → ZMod p, (r - (∑ i, c i • M i).rank) : ℕ) : ℝ)
      ≤ (((Pm B).det.totalDegree * p ^ s : ℕ) : ℝ) := by exact_mod_cast hSZ
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow] at hc
  have hdeg' : ((Pm B).det.totalDegree : ℝ) * (p : ℝ) ^ s ≤ (r : ℝ) * (p : ℝ) ^ s :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg) (pow_nonneg hp0.le s)
  have h1 : (p : ℝ) * ((p : ℝ) ^ s * r - ∑ c : Fin s → ZMod p, ((∑ i, c i • M i).rank : ℝ))
      ≤ (r : ℝ) * (p : ℝ) ^ s :=
    (mul_le_mul_of_nonneg_left hD hp0.le).trans (hc.trans hdeg')
  rw [le_div_iff₀ (pow_pos hp0 s)]
  have h2 : (1 - 1 / (p : ℝ)) * (r : ℝ) * (p : ℝ) ^ s
      = ((p : ℝ) * ((p : ℝ) ^ s * r) - r * (p : ℝ) ^ s) / p := by
    field_simp
  rw [h2, div_le_iff₀ hp0]
  linarith
