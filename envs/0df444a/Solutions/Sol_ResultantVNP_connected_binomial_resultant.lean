-- Prove2me | solution 1 for ResultantVNP.connected_binomial_resultant
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T13:21:38.546801+00:00
-- url     : https://prove2.me/submissions/c2be3221-a68f-4fe4-ae81-a6867812dee7

import Definitions.Def_ResultantVNP_resOf

set_option maxHeartbeats 400000
open MvPolynomial ResultantVNP Finset

namespace BinomialResultants

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


lemma sum_comp_count {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι) (y : ι → ℕ) :
    (∑ u,y (f u)) = ∑ v,(Finset.univ.filter (fun u => f u = v)).card * y v := by
  rw [← Finset.sum_fiberwise' Finset.univ f y]
  simp

lemma balanced_sum {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ι)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2) (y : ι → ℕ) :
    Finset.sum (Finset.univ : Finset ι) (fun u => y (f u) + y (g u)) =
      Finset.sum (Finset.univ : Finset ι) (fun v => 2 * y v) := by
  rw [Finset.sum_add_distrib,sum_comp_count,sum_comp_count,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [← add_mul,hb]

lemma closed_reverse {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ι)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2)
    (S : Finset ι) (hS : ∀ u ∈ S,f u ∈ S ∧ g u ∈ S) :
    ∀ u,(f u ∈ S ∨ g u ∈ S) → u ∈ S := by
  classical
  let y : ι → ℕ := fun u => if u ∈ S then 1 else 0
  have hle (u) : 2 * y u ≤ y (f u) + y (g u) := by
    by_cases hu : u ∈ S
    · simp [y,hu,(hS u hu).1,(hS u hu).2]
    · simp [y,hu]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun u _ => hle u)).mp
    (balanced_sum f g hb y).symm
  intro u hu
  by_contra hn
  have he := heq u (Finset.mem_univ _)
  rcases hu with hu | hu
  · simp [y,hn,hu] at he
    omega
  · simp [y,hn,hu] at he

lemma nonzero_propagation {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : ι → ι)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2)
    (hc : ∀ u v,Relation.ReflTransGen
      (fun a b => f a = b ∨ g a = b ∨ f b = a ∨ g b = a) u v)
    (t x : ι → ℂ) (hx : x ≠ 0) (he : ∀ i,x i ^ 2 = t i * x (f i) * x (g i)) :
    ∀ i,x i ≠ 0 := by
  classical
  let S := Finset.univ.filter (fun i => x i ≠ 0)
  have hforward (u) (hu : u ∈ S) : f u ∈ S ∧ g u ∈ S := by
    have hne : t u * x (f u) * x (g u) ≠ 0 :=
      (he u) ▸ pow_ne_zero 2 (Finset.mem_filter.mp hu).2
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using
      ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2,(mul_ne_zero_iff.mp hne).2⟩
  have hreverse := closed_reverse f g hb S hforward
  obtain ⟨u,hu⟩ : ∃ u,u ∈ S := by
    by_contra h
    push_neg at h
    apply hx
    funext i
    have hh := h i
    simpa [S] using hh
  have hprop (a b) (hab : f a = b ∨ g a = b ∨ f b = a ∨ g b = a)
      (ha : a ∈ S) : b ∈ S := by
    rcases hab with h | h | h | h
    · exact h ▸ (hforward a ha).1
    · exact h ▸ (hforward a ha).2
    · exact hreverse b (Or.inl (h.symm ▸ ha))
    · exact hreverse b (Or.inr (h.symm ▸ ha))
  intro v
  have hv : v ∈ S := by
    induction hc u v with
    | refl => exact hu
    | @tail b c hab hbc ih => exact hprop b c hbc ih
  exact (Finset.mem_filter.mp hv).2

lemma balanced_product {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ι)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2) (x : ι → ℂ) :
    (∏ u,x (f u) * x (g u)) = ∏ v,x v ^ 2 := by
  rw [Finset.prod_mul_distrib,← Finset.prod_fiberwise' Finset.univ f x,
    ← Finset.prod_fiberwise' Finset.univ g x]
  simp only [Finset.prod_const]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_add,hb]

lemma product_parameters {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : ι → ι)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2)
    (hc : ∀ u v,Relation.ReflTransGen
      (fun a b => f a = b ∨ g a = b ∨ f b = a ∨ g b = a) u v)
    (t x : ι → ℂ) (hx : x ≠ 0) (he : ∀ i,x i ^ 2 = t i * x (f i) * x (g i)) :
    ∏ i,t i = 1 := by
  have hne : (∏ i,x i ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero 2 (nonzero_propagation f g hb hc t x hx he i))
  have hp := Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => he i)
  simp_rw [mul_assoc] at hp
  rw [Finset.prod_mul_distrib,balanced_product f g hb x] at hp
  exact mul_right_cancel₀ hne (by simpa only [one_mul] using hp.symm)

lemma binomial_irreducible {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Irreducible (1 - ∏ i : ι,(X i : MvPolynomial ι ℂ)) := by
  let i := Classical.choice (inferInstance : Nonempty ι)
  let P : MvPolynomial ι ℂ := -(∏ j ∈ Finset.univ.erase i,X j)
  have hP : P ≠ 0 := by
    apply neg_ne_zero.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => X_ne_zero j)
  have hiv : i ∉ P.vars := by
    rw [show P.vars = (∏ j ∈ Finset.univ.erase i,(X j : MvPolynomial ι ℂ)).vars by simp [P]]
    intro hi
    have h := vars_prod (fun j : ι => (X j : MvPolynomial ι ℂ)) hi
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp h
    simp only [vars_X,Finset.mem_singleton] at hij
    exact (Finset.mem_erase.mp hj).1 hij.symm
  have h := irreducible_mul_X_add P 1 i hP hiv (by simp) (isRelPrime_one_right)
  convert h using 1
  rw [show P * X i = -(∏ j : ι,(X j : MvPolynomial ι ℂ)) by
    dsimp only [P]
    rw [neg_mul,Finset.prod_erase_mul _ _ (Finset.mem_univ i)]]
  ring

noncomputable def binomialForm {n : ℕ} (f g : Fin n → Fin n) (i : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n) ℂ) :=
  X i ^ 2 - C (X i) * X (f i) * X (g i)

noncomputable def binomialResultant (𝓡 : ResultantSystem) {n : ℕ} (f g : Fin n → Fin n) :
    MvPolynomial (Fin n) ℂ :=
  aeval (fun v : CoeffVar (fun _ : Fin n => 2) =>
    (binomialForm f g v.1).coeff v.2.1) (map (Int.castRingHom ℂ) (𝓡.res (fun _ => 2)))

lemma binomialForm_map {n : ℕ} (f g : Fin n → Fin n) (t : Fin n → ℂ) (i) :
    map (eval t) (binomialForm f g i) = X i ^ 2 - C (t i) * X (f i) * X (g i) := by
  simp [binomialForm]

lemma eval_binomialResultant (𝓡 : ResultantSystem) {n : ℕ} (f g : Fin n → Fin n)
    (t : Fin n → ℂ) :
    eval t (binomialResultant 𝓡 f g) = resOf 𝓡 (fun _ : Fin n => 2)
      (fun i => X i ^ 2 - C (t i) * X (f i) * X (g i)) := by
  unfold binomialResultant resOf
  change aeval t (aeval _ _) = aeval _ _
  rw [comp_aeval_apply]
  congr 2
  funext v
  change eval t ((binomialForm f g v.1).coeff v.2.1) = _
  rw [← coeff_map,binomialForm_map]

lemma binomial_homogeneous {n : ℕ} (f g : Fin n → Fin n) (t : Fin n → ℂ) (i) :
    (X i ^ 2 - C (t i) * X (f i) * X (g i) : MvPolynomial (Fin n) ℂ).IsHomogeneous 2 :=
  (isHomogeneous_X_pow i 2).sub
    (((isHomogeneous_C (Fin n) (t i)).mul (isHomogeneous_X ℂ (f i))).mul (isHomogeneous_X ℂ (g i)))

lemma binomial_zero_iff (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (f g : Fin n → Fin n) (t : Fin n → ℂ) :
    eval t (binomialResultant 𝓡 f g) = 0 ↔
      ∃ x : Fin n → ℂ,x ≠ 0 ∧ ∀ i,x i ^ 2 = t i * x (f i) * x (g i) := by
  rw [eval_binomialResultant]
  unfold resOf
  rw [(𝓡.spec (fun _ : Fin n => 2) hn (by omega)).1]
  simp_rw [form_coeff (fun _ : Fin n => 2) _ (binomial_homogeneous f g t)]
  simp only [map_sub,map_mul,map_pow,eval_X,eval_C,sub_eq_zero]

lemma binomial_at_zero (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (f g : Fin n → Fin n) : eval (fun _ => 0) (binomialResultant 𝓡 f g) = 1 := by
  rw [eval_binomialResultant]
  have h := congrArg (Int.castRingHom ℂ) ((𝓡.spec (fun _ : Fin n => 2) hn (by omega)).2.1)
  rw [map_eval] at h
  simpa [resOf,X_pow_eq_monomial,coeff_monomial,eq_comm,Function.comp_def] using h

theorem binomial_power (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (f g : Fin n → Fin n)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2)
    (hc : ∀ u v,Relation.ReflTransGen
      (fun a b => f a = b ∨ g a = b ∨ f b = a ∨ g b = a) u v) :
    ∃ c : ℕ, 1 ≤ c ∧ binomialResultant 𝓡 f g =
      (1 - ∏ i : Fin n,(X i : MvPolynomial (Fin n) ℂ)) ^ c := by
  let i₀ : Fin n := ⟨0,by omega⟩
  letI : Nonempty (Fin n) := ⟨i₀⟩
  have hzero : ∀ t : Fin n → ℂ,eval t (binomialResultant 𝓡 f g) = 0 →
      eval t (1 - ∏ i : Fin n,(X i : MvPolynomial (Fin n) ℂ)) = 0 := by
    intro t ht
    obtain ⟨x,hx,he⟩ := (binomial_zero_iff 𝓡 hn f g t).mp ht
    simp only [map_sub,map_one,map_prod,eval_X,product_parameters f g hb hc t x hx he,sub_self]
  obtain ⟨c,hc'⟩ := normalized_power binomial_irreducible hzero (fun _ => 0)
    (by simp [show n ≠ 0 by omega]) (binomial_at_zero 𝓡 hn f g)
  have hones : eval (fun _ => 1) (binomialResultant 𝓡 f g) = 0 := by
    apply (binomial_zero_iff 𝓡 hn f g _).mpr
    refine ⟨fun _ => 1,?_,?_⟩
    · intro h
      have hi := congrFun h i₀
      simp at hi
    · intro; simp
  refine ⟨c,?_,hc'⟩
  by_contra h
  have hc0 : c = 0 := by omega
  simp [hc',hc0] at hones

noncomputable def fullExponent (ι : Type) [Fintype ι] [DecidableEq ι] : ι →₀ ℕ :=
  Finsupp.indicator Finset.univ (fun _ _ => 1)

lemma fullExponent_apply {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    fullExponent ι i = 1 := by simp [fullExponent]

lemma fullExponent_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    fullExponent ι ≠ 0 := by
  intro h
  let i := Classical.choice (inferInstance : Nonempty ι)
  have hh := congrArg (fun e : ι →₀ ℕ => e i) h
  simp [fullExponent_apply] at hh

lemma coeff_binomial_power {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (c : ℕ) :
    ((1 - ∏ i : ι,(X i : MvPolynomial ι ℂ)) ^ c).coeff (fullExponent ι) = -(c : ℂ) := by
  classical
  have hprod : (∏ i : ι,(X i : MvPolynomial ι ℂ)) = monomial (fullExponent ι) 1 := by
    simpa only [pow_one,fullExponent] using prod_X_pow (R := ℂ) (fun _ : ι => 1) Finset.univ
  have hconst (k : ℕ) : ((1 - ∏ i : ι,(X i : MvPolynomial ι ℂ)) ^ k).coeff 0 = 1 := by
    change constantCoeff ((1 - ∏ i : ι,(X i : MvPolynomial ι ℂ)) ^ k) = 1
    simp
  induction c with
  | zero =>
    simp only [pow_zero,Nat.cast_zero,neg_zero]
    change (C (1 : ℂ)).coeff (fullExponent ι) = 0
    exact coeff_C_of_ne_zero fullExponent_ne_zero 1
  | succ c ih =>
    rw [pow_succ,mul_sub,mul_one,coeff_sub,ih]
    have hh := coeff_mul_monomial (0 : ι →₀ ℕ) (fullExponent ι) (1 : ℂ)
      ((1 - ∏ i : ι,(X i : MvPolynomial ι ℂ)) ^ c)
    simp only [zero_add,mul_one] at hh
    rw [← hprod] at hh
    rw [hh,hconst,Nat.cast_add,Nat.cast_one]
    ring

theorem negative_squarefree_coefficient (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (f g : Fin n → Fin n)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2)
    (hc : ∀ u v,Relation.ReflTransGen
      (fun a b => f a = b ∨ g a = b ∨ f b = a ∨ g b = a) u v) :
    ∃ c : ℕ, 1 ≤ c ∧ (binomialResultant 𝓡 f g).coeff (fullExponent (Fin n)) = -(c : ℂ) := by
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨c,hc,hP⟩ := binomial_power 𝓡 hn f g hb hc
  exact ⟨c,hc,by rw [hP,coeff_binomial_power]⟩

end BinomialResultants

theorem solution (𝓡 : ResultantVNP.ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (f g : Fin n → Fin n)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2)
    (hc : ∀ u v,Relation.ReflTransGen
      (fun a b => f a = b ∨ g a = b ∨ f b = a ∨ g b = a) u v) :
    let P : MvPolynomial (Fin n) ℂ :=
      MvPolynomial.aeval (fun v : ResultantVNP.CoeffVar (fun _ : Fin n => 2) =>
        (MvPolynomial.X v.1 ^ 2 - MvPolynomial.C (MvPolynomial.X v.1) *
          MvPolynomial.X (f v.1) * MvPolynomial.X (g v.1) :
            MvPolynomial (Fin n) (MvPolynomial (Fin n) ℂ)).coeff v.2.1)
        (MvPolynomial.map (Int.castRingHom ℂ) (𝓡.res (fun _ => 2)))
    ∃ c : ℕ, 1 ≤ c ∧ P = (1 - ∏ i : Fin n,(MvPolynomial.X i : MvPolynomial (Fin n) ℂ)) ^ c ∧
      P.coeff (Finsupp.indicator Finset.univ (fun _ _ => 1)) = -(c : ℂ) := by
  change ∃ c : ℕ, 1 ≤ c ∧ BinomialResultants.binomialResultant 𝓡 f g = _ ∧
    (BinomialResultants.binomialResultant 𝓡 f g).coeff (BinomialResultants.fullExponent (Fin n)) = _
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨c,hc,hP⟩ := BinomialResultants.binomial_power 𝓡 hn f g hb hc
  exact ⟨c,hc,hP,by rw [hP,BinomialResultants.coeff_binomial_power]⟩

#print axioms BinomialResultants.product_parameters
#print axioms BinomialResultants.binomial_irreducible
#print axioms BinomialResultants.binomial_power
#print axioms BinomialResultants.negative_squarefree_coefficient
#print axioms solution
