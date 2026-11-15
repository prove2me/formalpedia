-- Prove2me | solution 1 for ResultantVNP.lemma_2_6_3
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T12:35:47.458206+00:00
-- url     : https://prove2.me/submissions/2b7301cb-b296-49dc-b194-a8aecbf79356

import Definitions.Def_ResultantVNP_resOf
import Theorems.Thm_ResultantVNP_lemma_2_2
import Theorems.Thm_HararySachs_Hyper_det_generic_irreducible

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 2000
open MvPolynomial ResultantVNP Finset
open scoped Matrix

namespace ResultantScaling
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


lemma resOf_zero {n : ℕ} (𝓡 : ResultantSystem) (d : Fin n → ℕ)
    (hn : 1 ≤ n) (hd : ∀ i, 0 < d i) (f : Fin n → MvPolynomial (Fin n) ℂ)
    (hf : ∀ i, (f i).IsHomogeneous (d i)) :
    resOf 𝓡 d f = 0 ↔ ∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  have h := (𝓡.spec d hn hd).1 (fun v => (f v.1).coeff v.2.1)
  simpa only [resOf,ResultantScaling.form_coeff d f hf] using h



def CoeffHom {σ τ : Type} (P : MvPolynomial σ (MvPolynomial τ ℂ)) (D : ℕ) : Prop :=
  ∀ e, (P.coeff e).IsHomogeneous D

lemma coeffHom_C {σ τ : Type} {P : MvPolynomial τ ℂ} {D : ℕ} (hP : P.IsHomogeneous D) :
    CoeffHom (C P : MvPolynomial σ (MvPolynomial τ ℂ)) D := by
  classical
  intro e
  rw [coeff_C]
  split_ifs
  · exact hP
  · exact isHomogeneous_zero _ _ _

lemma coeffHom_sum {σ τ ι : Type} (S : Finset ι) (P : ι → MvPolynomial σ (MvPolynomial τ ℂ))
    {D : ℕ} (hP : ∀ i ∈ S, CoeffHom (P i) D) : CoeffHom (∑ i ∈ S, P i) D := by
  intro e
  rw [coeff_sum]
  exact IsHomogeneous.sum _ _ _ (fun i hi => hP i hi e)

lemma coeffHom_mul {σ τ : Type} {P Q : MvPolynomial σ (MvPolynomial τ ℂ)} {D E : ℕ}
    (hP : CoeffHom P D) (hQ : CoeffHom Q E) : CoeffHom (P * Q) (D+E) := by
  classical
  intro e
  rw [coeff_mul]
  exact IsHomogeneous.sum _ _ _ (fun p _ => (hP p.1).mul (hQ p.2))

lemma coeffHom_one {σ τ : Type} : CoeffHom (1 : MvPolynomial σ (MvPolynomial τ ℂ)) 0 := by
  simpa using coeffHom_C (σ := σ) (isHomogeneous_one τ ℂ)

lemma coeffHom_X {σ τ : Type} (i : σ) : CoeffHom (X i : MvPolynomial σ (MvPolynomial τ ℂ)) 0 := by
  classical
  intro e
  rw [coeff_X]
  split_ifs
  · exact isHomogeneous_one _ _
  · exact isHomogeneous_zero _ _ _

lemma coeffHom_pow {σ τ : Type} {P : MvPolynomial σ (MvPolynomial τ ℂ)} {D : ℕ}
    (hP : CoeffHom P D) (m : ℕ) : CoeffHom (P ^ m) (D*m) := by
  induction m with
  | zero => simpa using coeffHom_one
  | succ m ih => simpa [pow_succ,Nat.mul_succ] using coeffHom_mul ih hP

lemma coeffHom_prod {σ τ ι : Type} (S : Finset ι)
    (P : ι → MvPolynomial σ (MvPolynomial τ ℂ)) (D : ι → ℕ)
    (hP : ∀ i ∈ S, CoeffHom (P i) (D i)) : CoeffHom (∏ i ∈ S, P i) (∑ i ∈ S,D i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using coeffHom_one
  | @insert i S hi ih =>
    rw [prod_insert hi,sum_insert hi]
    exact coeffHom_mul (hP i (mem_insert_self _ _)) (ih (fun j hj => hP j (mem_insert_of_mem hj)))

noncomputable def linearForms {R : Type} [CommSemiring R] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) R) (i : Fin n) : MvPolynomial (Fin n) R :=
  ∑ j, C (Q i j) * X j

lemma linearForms_hom {R : Type} [CommSemiring R] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) R) (i : Fin n) : (linearForms Q i).IsHomogeneous 1 := by
  classical
  exact IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X R j).C_mul _)

lemma eval_linearForms {R : Type} [CommSemiring R] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (i : Fin n) :
    eval x (linearForms Q i) = (Q *ᵥ x) i := by
  simp [linearForms,Matrix.mulVec,dotProduct]

lemma map_linearForms {R S : Type} [CommSemiring R] [CommSemiring S] {n : ℕ}
    (φ : R →+* S) (Q : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    map φ (linearForms Q i) = linearForms (Q.map φ) i := by
  simp [linearForms,map_sum]

noncomputable def mat (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
  fun i j => X (i,j)

noncomputable def normPoly (𝓡 : ResultantSystem) {n : ℕ} (d : Fin n → ℕ) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  aeval (fun v : CoeffVar d => ((linearForms (mat n) v.1) ^ (d v.1)).coeff v.2.1)
    (map (Int.castRingHom ℂ) (𝓡.res d))

lemma eval_normPoly (𝓡 : ResultantSystem) {n : ℕ} (d : Fin n → ℕ)
    (c : Fin n × Fin n → ℂ) :
    eval c (normPoly 𝓡 d) = resOf 𝓡 d (fun i => linearForms (Matrix.of fun i j => c (i,j)) i ^ d i) := by
  unfold normPoly resOf
  change aeval c (aeval _ _) = aeval _ _
  rw [comp_aeval_apply]
  congr 2
  funext v
  change eval c (coeff _ _) = _
  rw [← coeff_map,map_pow,map_linearForms]
  have hmat : (mat n).map (eval c) = Matrix.of (fun i j => c (i,j)) := by ext i j; simp [mat]
  rw [hmat]

lemma block_weighted {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (w : Fin n → ℕ) :
    (map (Int.castRingHom ℂ) (𝓡.res d)).IsWeightedHomogeneous
      (fun v => w v.1) (∑ i, w i * ∏ j ∈ univ.erase i, d j) := by
  classical
  intro μ hμ
  have hμ' : coeff μ (𝓡.res d) ≠ 0 := by
    intro h
    apply hμ
    simp [coeff_map,h]
  have hb (i : Fin n) : Finsupp.weight (fun v : CoeffVar d =>
      if v.1 = i then 1 else 0) μ = ∏ j ∈ univ.erase i, d j :=
    (lemma_2_2 𝓡 hn d hd).1 i hμ'
  calc
    _ = ∑ v, μ v * w v.1 := by simp only [Finsupp.weight_eq_sum,smul_eq_mul]
    _ = ∑ v : CoeffVar d, ∑ i : Fin n, w i * (μ v * (if v.1 = i then 1 else 0)) := by
      simp [mul_comm]
    _ = ∑ i : Fin n, w i * Finsupp.weight (fun v => if v.1 = i then 1 else 0) μ := by
      rw [sum_comm]
      simp only [Finsupp.weight_eq_sum,smul_eq_mul,mul_sum]
    _ = _ := by simp_rw [hb]

lemma normPoly_hom (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) :
    (normPoly 𝓡 d).IsHomogeneous (n * ∏ j, d j) := by
  classical
  have hf (i : Fin n) : CoeffHom (linearForms (mat n) i) 1 := by
    apply coeffHom_sum
    intro j hj
    exact coeffHom_mul (coeffHom_C (isHomogeneous_X ℂ (i,j))) (coeffHom_X j)
  have h := homogeneous_aeval (block_weighted 𝓡 hn d hd d) _
    (fun v : CoeffVar d => by simpa using coeffHom_pow (hf v.1) (d v.1) v.2.1)
  have heq : (∑ i, d i * ∏ j ∈ univ.erase i, d j) = n * ∏ j, d j := by
    simp_rw [mul_prod_erase _ _ (mem_univ _)]
    simp
  simpa only [heq,normPoly] using h

lemma eval_det (n : ℕ) (c : Fin n × Fin n → ℂ) :
    eval c (mat n).det = Matrix.det (Matrix.of fun i j : Fin n => c (i,j)) := by
  rw [RingHom.map_det,RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [mat]

lemma det_hom (n : ℕ) : (mat n).det.IsHomogeneous n := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro σ hσ
  have hprod : (∏ i : Fin n, mat n (σ i) i).IsHomogeneous n := by
    simpa using IsHomogeneous.prod univ (fun i => mat n (σ i) i) (fun _ => 1)
      (fun i _ => isHomogeneous_X ℂ _)
  convert (isHomogeneous_C (Fin n × Fin n) (Equiv.Perm.sign σ : ℂ)).mul hprod using 1
  · simp
  · simp

lemma linearForms_one {R : Type} [CommRing R] (n : ℕ) (i : Fin n) :
    linearForms (1 : Matrix (Fin n) (Fin n) R) i = X i := by
  classical
  simp [linearForms,Matrix.one_apply]

lemma normalization (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) :
    resOf 𝓡 d (fun i => X i ^ d i) = 1 := by
  classical
  have h := congrArg (Int.castRingHom ℂ) ((𝓡.spec d hn hd).2.1)
  rw [map_eval] at h
  simpa [resOf,X_pow_eq_monomial,coeff_monomial,eq_comm,Function.comp_def] using h

lemma normPoly_eq (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) : normPoly 𝓡 d = (mat n).det ^ (∏ j,d j) := by
  classical
  let δ : Fin n × Fin n → ℂ := fun v => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2
  have hδP : eval δ (mat n).det = 1 := by rw [eval_det]; exact Matrix.det_one (R := ℂ)
  have hδQ : eval δ (normPoly 𝓡 d) = 1 := by
    rw [eval_normPoly]
    change resOf 𝓡 d (fun i => linearForms (1 : Matrix (Fin n) (Fin n) ℂ) i ^ d i) = 1
    simp_rw [linearForms_one]
    exact normalization 𝓡 hn d hd
  have hz : ∀ c, eval c (normPoly 𝓡 d) = 0 → eval c (mat n).det = 0 := by
    intro c hc
    rw [eval_normPoly,resOf_zero 𝓡 d hn hd _ (fun i => by
      simpa using (linearForms_hom (Matrix.of fun i j => c (i,j)) i).pow (d i))] at hc
    obtain ⟨x,hx,hf⟩ := hc
    rw [eval_det]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨x,hx,?_⟩
    funext i
    have h := hf i
    rw [map_pow,eval_linearForms] at h
    exact eq_zero_of_pow_eq_zero h
  obtain ⟨m,hm⟩ := normalized_power (HararySachs.Hyper.det_generic_irreducible ℂ n hn)
    hz δ hδP hδQ
  change normPoly 𝓡 d = (mat n).det ^ m at hm
  have hP0 : (mat n).det ≠ 0 := by intro h; simp [h] at hδP
  have hQ0 : normPoly 𝓡 d ≠ 0 := by intro h; simp [h] at hδQ
  have hdeg := congrArg totalDegree hm
  rw [(normPoly_hom 𝓡 hn d hd).totalDegree hQ0,
    ((det_hom n).pow m).totalDegree (pow_ne_zero _ hP0)] at hdeg
  have hm' : m = ∏ j,d j := (Nat.eq_of_mul_eq_mul_left hn hdeg).symm
  simpa only [hm'] using hm

lemma power_linear_resultant (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (Q : Matrix (Fin n) (Fin n) ℂ) :
    resOf 𝓡 d (fun i => linearForms Q i ^ d i) = Q.det ^ (∏ j,d j) := by
  have h := congrArg (eval fun v => Q v.1 v.2) (normPoly_eq 𝓡 hn d hd)
  rw [eval_normPoly,map_pow,eval_det] at h
  exact h

lemma map_substitute {R S : Type} [CommSemiring R] [CommSemiring S] {n : ℕ}
    (φ : R →+* S) (Q : Matrix (Fin n) (Fin n) R) (f : MvPolynomial (Fin n) R) :
    map φ (aeval (linearForms Q) f) = aeval (linearForms (Q.map φ)) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp only [map_mul,aeval_X,map_X,hf,map_linearForms]

lemma eval_substitute {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    eval x (aeval (linearForms Q) f) = eval (Q *ᵥ x) f := by
  change aeval x (aeval _ f) = aeval _ f
  rw [comp_aeval_apply]
  congr 2
  funext i
  exact eval_linearForms Q x i

noncomputable def liftMatrix {n : ℕ} {σ : Type} (Q : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ) := Q.map C

noncomputable def transformed (𝓡 : ResultantSystem) {n : ℕ} (d : Fin n → ℕ)
    (Q : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (CoeffVar d) ℂ :=
  aeval (fun v : CoeffVar d =>
    (aeval (linearForms (liftMatrix (σ := CoeffVar d) Q)) (generic d v.1)).coeff v.2.1)
    (map (Int.castRingHom ℂ) (𝓡.res d))

lemma eval_transformed (𝓡 : ResultantSystem) {n : ℕ} (d : Fin n → ℕ)
    (Q : Matrix (Fin n) (Fin n) ℂ) (c : CoeffVar d → ℂ) :
    eval c (transformed 𝓡 d Q) = resOf 𝓡 d (fun i => aeval (linearForms Q) (form d c i)) := by
  unfold transformed resOf
  change aeval c (aeval _ _) = aeval _ _
  rw [comp_aeval_apply]
  congr 2
  funext v
  change eval c (coeff _ _) = _
  rw [← coeff_map,map_substitute,generic_eval]
  have hQ : (liftMatrix (σ := CoeffVar d) Q).map (eval c) = Q := by ext i j; simp [liftMatrix]
  rw [hQ]

lemma transformed_hom (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (Q : Matrix (Fin n) (Fin n) ℂ) :
    (transformed 𝓡 d Q).IsHomogeneous (∑ i,∏ j ∈ univ.erase i,d j) := by
  classical
  have hlin (i : Fin n) : CoeffHom (linearForms (liftMatrix (σ := CoeffVar d) Q) i) 0 := by
    apply coeffHom_sum
    intro j hj
    exact coeffHom_mul (coeffHom_C (isHomogeneous_C _ (Q i j))) (coeffHom_X j)
  have hgen (i : Fin n) : CoeffHom (aeval (linearForms (liftMatrix (σ := CoeffVar d) Q)) (generic d i)) 1 := by
    rw [generic,map_sum]
    apply coeffHom_sum
    intro e he
    rw [aeval_monomial]
    have hp : CoeffHom (e.1.prod fun j m => linearForms (liftMatrix (σ := CoeffVar d) Q) j ^ m) 0 := by
      have h := coeffHom_prod e.1.support (fun j => linearForms (liftMatrix (σ := CoeffVar d) Q) j ^ e.1 j)
        (fun _ => 0) (fun j _ => by simpa using coeffHom_pow (hlin j) (e.1 j))
      simpa [Finsupp.prod] using h
    change CoeffHom (C (X (⟨i,e⟩ : CoeffVar d)) *
      (e.1.prod fun j m => linearForms (liftMatrix (σ := CoeffVar d) Q) j ^ m)) 1
    exact coeffHom_mul (coeffHom_C (σ := Fin n)
      (isHomogeneous_X ℂ (⟨i,e⟩ : CoeffVar d))) hp
  have hP := ((lemma_2_2 𝓡 hn d hd).2.2.1).map (Int.castRingHom ℂ)
  simpa only [one_mul,transformed] using hP.aeval _ (fun v => hgen v.1 v.2.1)

lemma scalar_of_zeros_degree {σ : Type} [Finite σ] {P Q : MvPolynomial σ ℂ}
    (hP : Irreducible P) (hz : ∀ c : σ → ℂ, eval c P = 0 → eval c Q = 0)
    (hdeg : Q.totalDegree ≤ P.totalDegree) : ∃ a : ℂ, Q = C a * P := by
  classical
  by_cases hQ : Q = 0
  · exact ⟨0,by simp [hQ]⟩
  let I : Ideal (MvPolynomial σ ℂ) := Ideal.span {P}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hP.prime
  have hmem : Q ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    intro c hc
    rw [aeval_eq_eval]
    apply hz
    simpa only [aeval_eq_eval] using hc P (Ideal.subset_span (by simp : P ∈ ({P} : Set _)))
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmem
  obtain ⟨A,hA⟩ := Ideal.mem_span_singleton.mp hmem
  have hA0 : A ≠ 0 := by intro h; simp [h] at hA; exact hQ hA
  have hAd : A.totalDegree = 0 := by
    rw [hA,totalDegree_mul_of_isDomain hP.ne_zero hA0] at hdeg
    omega
  refine ⟨A.constantCoeff,?_⟩
  conv_lhs => rw [hA,(totalDegree_eq_zero_iff_eq_C.mp hAd)]
  simp only [constantCoeff_eq,mul_comm]

lemma transformed_eq (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q.det ≠ 0) :
    transformed 𝓡 d Q = C (Q.det ^ (∏ j,d j)) * map (Int.castRingHom ℂ) (𝓡.res d) := by
  classical
  let P := map (Int.castRingHom ℂ) (𝓡.res d)
  have hP := (𝓡.spec d hn hd).2.2
  have hPhom := ((lemma_2_2 𝓡 hn d hd).2.2.1).map (Int.castRingHom ℂ)
  have hdeg : (transformed 𝓡 d Q).totalDegree ≤ P.totalDegree := by
    rw [hPhom.totalDegree hP.ne_zero]
    exact (transformed_hom 𝓡 hn d hd Q).totalDegree_le
  have hz : ∀ c, eval c P = 0 → eval c (transformed 𝓡 d Q) = 0 := by
    intro c hc
    obtain ⟨x,hx,hf⟩ := (𝓡.spec d hn hd).1 c |>.mp hc
    have hxy : Q *ᵥ (Q⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hQ),Matrix.one_mulVec]
    rw [eval_transformed,resOf_zero 𝓡 d hn hd _ (fun i => by
      have hh := (generic_homogeneous d i).map (eval c)
      rw [generic_eval] at hh
      simpa only [one_mul] using hh.aeval (linearForms Q) (linearForms_hom Q))]
    refine ⟨Q⁻¹ *ᵥ x,?_,?_⟩
    · intro hy
      rw [hy,Matrix.mulVec_zero] at hxy
      exact hx hxy.symm
    · intro i
      rw [eval_substitute,hxy]
      exact hf i
  obtain ⟨a,ha⟩ := scalar_of_zeros_degree hP hz hdeg
  let δ : CoeffVar d → ℂ := fun v => if v.2.1 = Finsupp.single v.1 (d v.1) then 1 else 0
  have hδP : eval δ P = 1 := by
    have h := congrArg (Int.castRingHom ℂ) ((𝓡.spec d hn hd).2.1)
    rw [map_eval] at h
    simpa [P,δ,Function.comp_def] using h
  have hforms : form d δ = fun i => X i ^ d i := by
    funext i
    have h := form_coeff d (fun j => (X j ^ d j : MvPolynomial (Fin n) ℂ))
      (fun j => isHomogeneous_X_pow j (d j)) i
    simpa [δ,X_pow_eq_monomial,coeff_monomial,eq_comm] using h
  have heval := congrArg (eval δ) ha
  rw [eval_transformed,hforms,map_mul,eval_C,hδP,mul_one] at heval
  simp only [map_pow,aeval_X] at heval
  rw [power_linear_resultant 𝓡 hn d hd Q] at heval
  rw [← heval] at ha
  exact ha

end ResultantScaling

theorem solution (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, (f i).IsHomogeneous (d i))
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    resOf 𝓡 d (fun i => MvPolynomial.aeval
        (fun k => ∑ j, MvPolynomial.C (Q k j) * MvPolynomial.X j) (f i)) =
      Q.det ^ (∏ j, d j) * resOf 𝓡 d f := by
  classical
  change resOf 𝓡 d (fun i => aeval (ResultantScaling.linearForms Q) (f i)) = _
  by_cases hQ : Q.det = 0
  · have hprod : 0 < ∏ j,d j := prod_pos (fun j _ => hd j)
    rw [hQ,zero_pow (Nat.ne_of_gt hprod),zero_mul]
    rw [ResultantScaling.resOf_zero 𝓡 d hn hd _ (fun i => by
      simpa only [one_mul] using (hf i).aeval _ (ResultantScaling.linearForms_hom Q))]
    obtain ⟨x,hx,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hQ
    refine ⟨x,hx,?_⟩
    intro i
    rw [ResultantScaling.eval_substitute,hker,eval_zero]
    exact (hf i).coeff_eq_zero (by simpa using (Nat.ne_of_gt (hd i)).symm)
  · have h := congrArg (eval fun v : CoeffVar d => (f v.1).coeff v.2.1)
      (ResultantScaling.transformed_eq 𝓡 hn d hd Q hQ)
    rw [ResultantScaling.eval_transformed,map_mul,eval_C] at h
    have heq : form d (fun v : CoeffVar d => (f v.1).coeff v.2.1) = f :=
      funext (ResultantScaling.form_coeff d f hf)
    rw [heq] at h
    exact h

#print axioms solution
