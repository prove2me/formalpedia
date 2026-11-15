-- Prove2me | solution 1 for ResultantVNP.lemma_2_6_5
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T12:27:41.979365+00:00
-- url     : https://prove2.me/submissions/05ca32d0-9420-413f-9bf6-639bff8b3643

import Definitions.Def_ResultantVNP_resOf
import Theorems.Thm_ResultantVNP_lemma_2_2

set_option maxHeartbeats 400000
open MvPolynomial ResultantVNP Finset

namespace ResultantPadding

lemma form_coeff {n : ℕ} (d : Fin n → ℕ)
    (F : Fin n → MvPolynomial (Fin n) ℂ) (hF : ∀ i, (F i).IsHomogeneous (d i))
    (i : Fin n) : form d (fun v => (F v.1).coeff v.2.1) i = F i := by
  classical
  ext e
  rw [form, coeff_sum]
  by_cases he : ∑ j, e j = d i
  · rw [sum_eq_single (⟨e,he⟩ : {e : Fin n →₀ ℕ // ∑ j, e j = d i})]
    · simp
    · intro v hv hne
      have hne' : v.1 ≠ e := fun heq => hne (Subtype.ext heq)
      simp [coeff_monomial,hne']
    · simp
  · rw [(hF i).coeff_eq_zero (by simpa only [Finsupp.degree_eq_sum] using he)]
    apply sum_eq_zero
    intro v hv
    have hne : v.1 ≠ e := by intro h; exact he (h ▸ v.2)
    simp [coeff_monomial,hne]


lemma normalized_power {σ : Type} [Finite σ] {P Q : MvPolynomial σ ℂ}
    (hP : Irreducible P) (hz : ∀ x : σ → ℂ, eval x Q = 0 → eval x P = 0)
    (δ : σ → ℂ) (hδP : eval δ P = 1) (hδQ : eval δ Q = 1) :
    ∃ m : ℕ, Q = P ^ m := by
  let I : Ideal (MvPolynomial σ ℂ) := Ideal.span {Q}
  have hmem : P ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    intro x hx
    rw [aeval_eq_eval]
    apply hz
    have h := hx Q (Ideal.subset_span (by simp : Q ∈ ({Q} : Set _)))
    simpa only [aeval_eq_eval] using h
  rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
  obtain ⟨r,hr⟩ := hmem
  obtain ⟨m,hm,hassoc⟩ := (dvd_prime_pow hP.prime r).mp (Ideal.mem_span_singleton.mp hr)
  obtain ⟨u,hu⟩ := hassoc.symm
  obtain ⟨a,haunit,ha⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have heq : Q = C a * P ^ m := by simpa [ha,mul_comm] using hu.symm
  have ha1 : a = 1 := by simpa [heq,hδP] using hδQ
  exact ⟨m, by simp [heq,ha1]⟩

lemma homogeneous_aeval {σ τ : Type} {R : Type} [CommSemiring R]
    {P : MvPolynomial σ R} {w : σ → ℕ} {D : ℕ}
    (hP : P.IsWeightedHomogeneous w D) (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsHomogeneous (w i)) : (aeval f P).IsHomogeneous D := by
  classical
  rw [← P.support_sum_monomial_coeff,map_sum]
  apply IsHomogeneous.sum
  intro μ hμ
  rw [aeval_monomial]
  have hprod : (μ.prod fun i e => f i ^ e).IsHomogeneous (Finsupp.weight w μ) := by
    have h := IsHomogeneous.prod μ.support (fun i => (f i) ^ μ i)
      (fun i => w i * μ i) (fun i _ => (hf i).pow (μ i))
    simpa [Finsupp.prod,Finsupp.weight_apply,Finsupp.sum,mul_comm] using h
  have h := (isHomogeneous_C τ (P.coeff μ)).mul hprod
  simpa [hP (mem_support_iff.mp hμ)] using h

noncomputable def generic {k : ℕ} (d : Fin k → ℕ) (i : Fin k) :
    MvPolynomial (Fin k) (MvPolynomial (CoeffVar d) ℂ) :=
  ∑ e : {e : Fin k →₀ ℕ // ∑ j, e j = d i}, monomial e.1 (X ⟨i,e⟩)

lemma generic_eval {k : ℕ} (d : Fin k → ℕ) (c : CoeffVar d → ℂ) (i : Fin k) :
    map (eval c) (generic d i) = form d c i := by
  classical
  simp [generic,form,map_sum,map_monomial]

lemma generic_homogeneous {k : ℕ} (d : Fin k → ℕ) (i : Fin k) :
    (generic d i).IsHomogeneous (d i) := by
  classical
  apply IsHomogeneous.sum
  intro e he
  apply isHomogeneous_monomial
  simpa only [Finsupp.degree_eq_sum] using e.2

lemma generic_coeff_homogeneous {k : ℕ} (d : Fin k → ℕ) (i : Fin k)
    (e : Fin k →₀ ℕ) : ((generic d i).coeff e).IsHomogeneous 1 := by
  classical
  rw [generic,coeff_sum]
  apply IsHomogeneous.sum
  intro v hv
  rw [coeff_monomial]
  split_ifs
  · exact isHomogeneous_X ℂ _
  · exact isHomogeneous_zero _ _ _

noncomputable def pad {R : Type} [CommSemiring R] {k n : ℕ} (hkn : k ≤ n)
    (f : Fin k → MvPolynomial (Fin k) R) (i : Fin n) : MvPolynomial (Fin n) R :=
  if h : i.val < k then rename (Fin.castLE hkn) (f ⟨i,h⟩) else X i ^ 2

lemma pad_homogeneous {R : Type} [CommSemiring R] {k n : ℕ} (hkn : k ≤ n)
    (f : Fin k → MvPolynomial (Fin k) R) (hf : ∀ i, (f i).IsHomogeneous 2)
    (i : Fin n) : (pad hkn f i).IsHomogeneous 2 := by
  classical
  unfold pad
  split_ifs
  · exact (hf _).rename_isHomogeneous
  · exact isHomogeneous_X_pow _ _

lemma map_pad {R S : Type} [CommSemiring R] [CommSemiring S] {k n : ℕ}
    (hkn : k ≤ n) (φ : R →+* S) (f : Fin k → MvPolynomial (Fin k) R) (i : Fin n) :
    map φ (pad hkn f i) = pad hkn (fun j => map φ (f j)) i := by
  classical
  unfold pad
  split_ifs <;> simp [map_rename]

lemma resOf_zero {n : ℕ} (𝓡 : ResultantSystem) (d : Fin n → ℕ)
    (hn : 1 ≤ n) (hd : ∀ i, 0 < d i) (f : Fin n → MvPolynomial (Fin n) ℂ)
    (hf : ∀ i, (f i).IsHomogeneous (d i)) :
    resOf 𝓡 d f = 0 ↔ ∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  have h := (𝓡.spec d hn hd).1 (fun v => (f v.1).coeff v.2.1)
  simpa only [resOf,ResultantPadding.form_coeff d f hf] using h

lemma pad_roots {k n : ℕ} (hkn : k ≤ n)
    (f : Fin k → MvPolynomial (Fin k) ℂ) :
    (∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ i, eval x (pad hkn f i) = 0) →
      ∃ y : Fin k → ℂ, y ≠ 0 ∧ ∀ i, eval y (f i) = 0 := by
  classical
  rintro ⟨x,hx,hf⟩
  refine ⟨fun j => x (Fin.castLE hkn j), ?_, ?_⟩
  · intro hy
    apply hx
    funext i
    by_cases hi : i.val < k
    · exact congrFun hy ⟨i,hi⟩
    · have h := hf i
      simp only [pad,dif_neg hi,map_pow,eval_X] at h
      exact eq_zero_of_pow_eq_zero h
  · intro j
    have h := hf (Fin.castLE hkn j)
    simp only [pad,Fin.val_castLE,dif_pos j.isLt,eval_rename] at h
    exact h

noncomputable def paddedResultant (𝓡 : ResultantSystem) {k n : ℕ} (hkn : k ≤ n) :
    MvPolynomial (CoeffVar (fun _ : Fin k => 2)) ℂ :=
  aeval (fun v : CoeffVar (fun _ : Fin n => 2) =>
    (pad hkn (generic (fun _ => 2)) v.1).coeff v.2.1)
    (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 2)))

lemma eval_paddedResultant (𝓡 : ResultantSystem) {k n : ℕ} (hkn : k ≤ n)
    (c : CoeffVar (fun _ : Fin k => 2) → ℂ) :
    eval c (paddedResultant 𝓡 hkn) =
      resOf 𝓡 (fun _ : Fin n => 2) (pad hkn (form (fun _ => 2) c)) := by
  classical
  unfold paddedResultant resOf
  change aeval c (aeval _ _) = aeval _ _
  rw [comp_aeval_apply]
  congr 2
  funext v
  change eval c ((pad hkn (generic (fun _ => 2)) v.1).coeff v.2.1) = _
  rw [← coeff_map,map_pad]
  simp only [generic_eval]

lemma diagonal_form (k : ℕ) (i : Fin k) :
    form (fun _ => 2) (fun v : CoeffVar (fun _ : Fin k => 2) =>
      if v.2.1 = Finsupp.single v.1 2 then (1 : ℂ) else 0) i = X i ^ 2 := by
  have h := ResultantPadding.form_coeff (fun _ : Fin k => 2)
    (fun j => (X j ^ 2 : MvPolynomial (Fin k) ℂ)) (fun _ => isHomogeneous_X_pow _ _) i
  simpa [X_pow_eq_monomial,coeff_monomial,eq_comm] using h

lemma resultant_normalization (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) :
    resOf 𝓡 (fun _ : Fin n => 2) (fun i => X i ^ 2) = 1 := by
  classical
  have h := congrArg (Int.castRingHom ℂ) ((𝓡.spec (fun _ : Fin n => 2) hn (by omega)).2.1)
  rw [map_eval] at h
  simpa [resOf,X_pow_eq_monomial,coeff_monomial,eq_comm,Function.comp_def] using h

lemma pad_diagonal {R : Type} [CommSemiring R] {k n : ℕ} (hkn : k ≤ n) :
    pad hkn (fun i => (X i ^ 2 : MvPolynomial (Fin k) R)) = fun i => X i ^ 2 := by
  classical
  funext i
  unfold pad
  split_ifs <;> simp

lemma block_weighted {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n) (w : Fin n → ℕ) :
    (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 2))).IsWeightedHomogeneous
      (fun v => w v.1) (∑ i, w i * 2 ^ (n-1)) := by
  classical
  intro μ hμ
  have hμ' : coeff μ (𝓡.res (fun _ : Fin n => 2)) ≠ 0 := by
    intro h
    apply hμ
    simp [coeff_map,h]
  have hb (i : Fin n) : Finsupp.weight (fun v : CoeffVar (fun _ : Fin n => 2) =>
      if v.1 = i then 1 else 0) μ = 2 ^ (n-1) := by
    have h := (lemma_2_2 𝓡 hn (fun _ => 2) (by omega)).1 i hμ'
    simpa [prod_const,card_erase_of_mem (mem_univ _)] using h
  calc
    _ = ∑ v, μ v * w v.1 := by simp only [Finsupp.weight_eq_sum,smul_eq_mul]
    _ = ∑ v : CoeffVar (fun _ : Fin n => 2),
        ∑ i : Fin n, w i * (μ v * (if v.1 = i then 1 else 0)) := by simp [mul_comm]
    _ = ∑ i : Fin n, w i * Finsupp.weight (fun v => if v.1 = i then 1 else 0) μ := by
      rw [sum_comm]
      simp only [Finsupp.weight_eq_sum,smul_eq_mul,mul_sum]
    _ = _ := by simp_rw [hb]

lemma pad_coeff_homogeneous {k n : ℕ} (hkn : k ≤ n)
    (v : CoeffVar (fun _ : Fin n => 2)) :
    ((pad hkn (generic (fun _ => 2)) v.1).coeff v.2.1).IsHomogeneous
      (if v.1.val < k then 1 else 0) := by
  classical
  unfold pad
  split_ifs with h
  · rw [generic,map_sum,coeff_sum]
    apply IsHomogeneous.sum
    intro e he
    rw [rename_monomial,coeff_monomial]
    split_ifs
    · exact isHomogeneous_X ℂ _
    · exact isHomogeneous_zero _ _ _
  · rw [X_pow_eq_monomial,coeff_monomial]
    split_ifs
    · exact isHomogeneous_one _ _
    · exact isHomogeneous_zero _ _ _

lemma padded_homogeneous (𝓡 : ResultantSystem) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (paddedResultant 𝓡 hkn).IsHomogeneous (k * 2 ^ (n-1)) := by
  classical
  have h := homogeneous_aeval (block_weighted 𝓡 (hk.trans hkn)
      (fun i => if i.val < k then 1 else 0)) _ (pad_coeff_homogeneous hkn)
  have heq : (∑ i : Fin n, (if i.val < k then 1 else 0) * 2 ^ (n-1)) =
      k * 2 ^ (n-1) := by
    simp only [ite_mul,one_mul,zero_mul,← sum_filter]
    rw [sum_const,nsmul_eq_mul,Fin.card_filter_val_lt,min_eq_right hkn]
    simp
  simpa only [heq,paddedResultant] using h

lemma padded_power (𝓡 : ResultantSystem) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    paddedResultant 𝓡 hkn =
      map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin k => 2)) ^ (2 ^ (n-k)) := by
  classical
  let P := map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin k => 2))
  let δ : CoeffVar (fun _ : Fin k => 2) → ℂ :=
    fun v => if v.2.1 = Finsupp.single v.1 2 then 1 else 0
  have hPδ : eval δ P = 1 := by
    have h := congrArg (Int.castRingHom ℂ) ((𝓡.spec (fun _ : Fin k => 2) hk (by omega)).2.1)
    rw [map_eval] at h
    simpa [P,δ,Function.comp_def] using h
  have hQδ : eval δ (paddedResultant 𝓡 hkn) = 1 := by
    rw [eval_paddedResultant]
    have hf : form (fun _ => 2) δ = fun i => X i ^ 2 := funext (diagonal_form k)
    rw [hf,pad_diagonal,resultant_normalization 𝓡 (hk.trans hkn)]
  have hz : ∀ c, eval c (paddedResultant 𝓡 hkn) = 0 → eval c P = 0 := by
    intro c hc
    rw [eval_paddedResultant,resOf_zero 𝓡 _ (hk.trans hkn) (by omega)] at hc
    · exact ((𝓡.spec (fun _ : Fin k => 2) hk (by omega)).1 c).mpr (pad_roots hkn _ hc)
    · apply pad_homogeneous
      intro i
      simpa only [generic_eval] using (generic_homogeneous (fun _ : Fin k => 2) i).map (eval c)
  obtain ⟨m,hm⟩ := normalized_power (𝓡.spec (fun _ : Fin k => 2) hk (by omega)).2.2
    hz δ hPδ hQδ
  have hP0 : P ≠ 0 := by intro h; simpa [h] using hPδ
  have hQ0 : paddedResultant 𝓡 hkn ≠ 0 := by intro h; simpa [h] using hQδ
  have hPhom : P.IsHomogeneous (k * 2 ^ (k-1)) :=
    ((lemma_2_2 𝓡 hk (fun _ : Fin k => 2) (by omega)).2.2.2).map _
  have hdeg := congrArg totalDegree hm
  rw [(padded_homogeneous 𝓡 hk hkn).totalDegree hQ0,
    (hPhom.pow m).totalDegree (pow_ne_zero _ hP0)] at hdeg
  have hpow : 2 ^ (n-1) = 2 ^ (k-1) * 2 ^ (n-k) := by
    rw [← pow_add]
    congr 1
    omega
  have hm' : m = 2 ^ (n-k) := by
    rw [hpow,← mul_assoc] at hdeg
    exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hk (by positivity)) hdeg).symm
  simpa only [hm'] using hm

end ResultantPadding

theorem solution (𝓡 : ResultantSystem) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (f : Fin k → MvPolynomial (Fin k) ℂ) (hf : ∀ i, (f i).IsHomogeneous 2) :
    resOf 𝓡 (fun _ : Fin n => 2)
        (fun i => if h : (i : ℕ) < k then MvPolynomial.rename (Fin.castLE hkn) (f ⟨i, h⟩)
          else MvPolynomial.X i ^ 2) =
      resOf 𝓡 (fun _ : Fin k => 2) f ^ (2 ^ (n - k)) := by
  have h := congrArg (eval (fun v : CoeffVar (fun _ : Fin k => 2) => (f v.1).coeff v.2.1))
    (ResultantPadding.padded_power 𝓡 hk hkn)
  rw [ResultantPadding.eval_paddedResultant,map_pow] at h
  have heq : form (fun _ => 2) (fun v : CoeffVar (fun _ : Fin k => 2) => (f v.1).coeff v.2.1) = f :=
    funext (ResultantPadding.form_coeff (fun _ => 2) f hf)
  rw [heq] at h
  exact h

#print axioms solution
