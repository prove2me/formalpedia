-- Prove2me | solution 1 for ResultantVNP.lemma_2_6_1
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T12:45:41.824267+00:00
-- url     : https://prove2.me/submissions/9bdf4ee1-42dc-4e67-a5f4-b5e749aa90c8

import Definitions.Def_ResultantVNP_resOf
import Theorems.Thm_ResultantVNP_lemma_2_2

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 2000
open MvPolynomial ResultantVNP Finset

namespace ResultantMultiplicativity

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
  simpa only [resOf,ResultantMultiplicativity.form_coeff d f hf] using h



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



lemma prime_rename {σ τ : Type} {P : MvPolynomial σ ℂ} (hP : Prime P)
    (f : σ → τ) (hf : Function.Injective f) : Prime (rename f P) := by
  classical
  let E : σ ≃ Set.range f := Equiv.ofInjective f hf
  have h := (prime_rename_iff (Set.range f)).mpr
    ((hP.irreducible.map (renameEquiv ℂ E).toMulEquiv).prime)
  change Prime (rename Subtype.val (rename E P)) at h
  rw [rename_rename] at h
  exact h

lemma generic_coeff {n : ℕ} (d : Fin n → ℕ) (j : Fin n) (e : Fin n →₀ ℕ) :
    (generic d j).coeff e = if he : ∑ k,e k = d j then X ⟨j,e,he⟩ else 0 := by
  classical
  rw [generic,coeff_sum]
  split_ifs with he
  · rw [sum_eq_single (⟨e,he⟩ : {e : Fin n →₀ ℕ // ∑ k,e k = d j})]
    · simp
    · intro v hv hne
      have hne' : v.1 ≠ e := fun h => hne (Subtype.ext h)
      simp [coeff_monomial,hne']
    · simp
  · apply sum_eq_zero
    intro v hv
    have hne : v.1 ≠ e := by intro h; exact he (h ▸ v.2)
    simp [coeff_monomial,hne]

variable {n : ℕ} (d : Fin n → ℕ) (i : Fin n) (a b : ℕ)

abbrev Vars := CoeffVar (Function.update d i a) ⊕ CoeffVar (Function.update d i b)

noncomputable def embedH (v : CoeffVar (Function.update d i b)) : Vars d i a b :=
  if h : v.1 = i then Sum.inr v else Sum.inl ⟨v.1,v.2.1,by
    simpa only [Function.update_of_ne h] using v.2.2⟩

def row (v : Vars d i a b) : Fin n := Sum.elim Sigma.fst Sigma.fst v

def exponent (v : Vars d i a b) : Fin n →₀ ℕ := Sum.elim (fun v => v.2.1) (fun v => v.2.1) v

lemma embedH_row (v : CoeffVar (Function.update d i b)) : row d i a b (embedH d i a b v) = v.1 := by
  classical
  unfold embedH
  split_ifs <;> rfl

lemma embedH_exponent (v : CoeffVar (Function.update d i b)) :
    exponent d i a b (embedH d i a b v) = v.2.1 := by
  classical
  unfold embedH
  split_ifs <;> rfl

lemma embedH_injective : Function.Injective (embedH d i a b) := by
  intro v w h
  have hr := congrArg (row d i a b) h
  have he := congrArg (exponent d i a b) h
  simp only [embedH_row] at hr
  simp only [embedH_exponent] at he
  rcases v with ⟨v,e,he'⟩
  rcases w with ⟨w,f,hf⟩
  dsimp at hr he
  subst w
  subst f
  rfl

noncomputable def G (j : Fin n) : MvPolynomial (Fin n) (MvPolynomial (Vars d i a b) ℂ) :=
  map (rename Sum.inl).toRingHom (generic (Function.update d i a) j)

noncomputable def H (j : Fin n) : MvPolynomial (Fin n) (MvPolynomial (Vars d i a b) ℂ) :=
  map (rename (embedH d i a b)).toRingHom (generic (Function.update d i b) j)

lemma HG_other (j : Fin n) (hj : j ≠ i) : H d i a b j = G d i a b j := by
  classical
  ext e
  simp only [G,H,coeff_map,generic_coeff,Function.update_of_ne hj]
  split_ifs with he
  · simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,rename_X]
    congr 1
    simp only [embedH,dif_neg hj]
  · simp

noncomputable def combined (j : Fin n) : MvPolynomial (Fin n) (MvPolynomial (Vars d i a b) ℂ) :=
  if j = i then G d i a b i * H d i a b i else G d i a b j

noncomputable def RP (𝓡 : ResultantSystem) : MvPolynomial (Vars d i a b) ℂ :=
  rename Sum.inl (map (Int.castRingHom ℂ) (𝓡.res (Function.update d i a)))

noncomputable def HP (𝓡 : ResultantSystem) : MvPolynomial (Vars d i a b) ℂ :=
  rename (embedH d i a b) (map (Int.castRingHom ℂ) (𝓡.res (Function.update d i b)))

noncomputable def QP (𝓡 : ResultantSystem) : MvPolynomial (Vars d i a b) ℂ :=
  aeval (fun v : CoeffVar (Function.update d i (a+b)) => (combined d i a b v.1).coeff v.2.1)
    (map (Int.castRingHom ℂ) (𝓡.res (Function.update d i (a+b))))

lemma eval_G (c : Vars d i a b → ℂ) (j : Fin n) :
    map (eval c) (G d i a b j) = form (Function.update d i a) (c ∘ Sum.inl) j := by
  rw [G,MvPolynomial.map_map]
  have h : (eval c).comp (rename (R := ℂ) Sum.inl).toRingHom = eval (c ∘ Sum.inl) := by
    ext v
    · change eval c (rename Sum.inl (C v)) = eval (c ∘ Sum.inl) (C v)
      simp
    · change eval c (rename Sum.inl (X v)) = eval (c ∘ Sum.inl) (X v)
      simp
  rw [h,generic_eval]

lemma eval_H (c : Vars d i a b → ℂ) (j : Fin n) :
    map (eval c) (H d i a b j) = form (Function.update d i b) (c ∘ embedH d i a b) j := by
  rw [H,MvPolynomial.map_map]
  have h : (eval c).comp (rename (R := ℂ) (embedH d i a b)).toRingHom = eval (c ∘ embedH d i a b) := by
    ext v
    · change eval c (rename (embedH d i a b) (C v)) = eval (c ∘ embedH d i a b) (C v)
      simp
    · change eval c (rename (embedH d i a b) (X v)) = eval (c ∘ embedH d i a b) (X v)
      simp
  rw [h,generic_eval]

lemma G_hom (j : Fin n) : (G d i a b j).IsHomogeneous (Function.update d i a j) :=
  (generic_homogeneous _ j).map _

lemma H_hom (j : Fin n) : (H d i a b j).IsHomogeneous (Function.update d i b j) :=
  (generic_homogeneous _ j).map _

lemma combined_hom (j : Fin n) : (combined d i a b j).IsHomogeneous (Function.update d i (a+b) j) := by
  classical
  by_cases hj : j = i
  · subst j
    simpa only [combined,if_pos rfl,ite_true,Function.update_self] using (G_hom d i a b i).mul (H_hom d i a b i)
  · simpa only [combined,if_neg hj,Function.update_of_ne hj] using G_hom d i a b j

lemma eval_QP (𝓡 : ResultantSystem) (c : Vars d i a b → ℂ) :
    eval c (QP d i a b 𝓡) = resOf 𝓡 (Function.update d i (a+b))
      (fun j => map (eval c) (combined d i a b j)) := by
  unfold QP resOf
  change aeval c (aeval _ _) = aeval _ _
  rw [comp_aeval_apply]
  congr 2

lemma positive_update (hd : ∀ j,j ≠ i → 0 < d j) {t : ℕ} (ht : 0 < t) :
    ∀ j,0 < Function.update d i t j := by
  classical
  intro j
  by_cases hj : j = i
  · simpa [hj] using ht
  · simpa only [Function.update_of_ne hj] using hd j hj

lemma dvd_of_zeros {σ : Type} [Finite σ] {P Q : MvPolynomial σ ℂ} (hP : Prime P)
    (hz : ∀ c : σ → ℂ, eval c P = 0 → eval c Q = 0) : P ∣ Q := by
  let I : Ideal (MvPolynomial σ ℂ) := Ideal.span {P}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hP
  have hmem : Q ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    intro c hc
    rw [aeval_eq_eval]
    apply hz
    simpa only [aeval_eq_eval] using hc P (Ideal.subset_span (by simp : P ∈ ({P} : Set _)))
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmem
  exact Ideal.mem_span_singleton.mp hmem

lemma RP_prime (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) : Prime (RP d i a b 𝓡) :=
  prime_rename (𝓡.spec _ hn (positive_update d i hd ha)).2.2.prime Sum.inl Sum.inl_injective

lemma HP_prime (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (hb : 0 < b) : Prime (HP d i a b 𝓡) :=
  prime_rename (𝓡.spec _ hn (positive_update d i hd hb)).2.2.prime _ (embedH_injective d i a b)

lemma RP_dvd (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) (hb : 0 < b) :
    RP d i a b 𝓡 ∣ QP d i a b 𝓡 := by
  classical
  apply dvd_of_zeros (RP_prime d i a b 𝓡 hn hd ha)
  intro c hc
  rw [RP,eval_rename] at hc
  obtain ⟨x,hx,hf⟩ := (𝓡.spec _ hn (positive_update d i hd ha)).1 _ |>.mp hc
  rw [eval_QP,resOf_zero 𝓡 _ hn (positive_update d i hd (by omega : 0 < a+b)) _
    (fun j => (combined_hom d i a b j).map (eval c))]
  refine ⟨x,hx,?_⟩
  intro j
  by_cases hj : j = i
  · subst j
    simp only [combined,if_pos rfl,ite_true,map_mul,eval_G,hf,zero_mul]
  · simp only [combined,if_neg hj,eval_G,hf]

lemma HP_dvd (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) (hb : 0 < b) :
    HP d i a b 𝓡 ∣ QP d i a b 𝓡 := by
  classical
  apply dvd_of_zeros (HP_prime d i a b 𝓡 hn hd hb)
  intro c hc
  rw [HP,eval_rename] at hc
  obtain ⟨x,hx,hf⟩ := (𝓡.spec _ hn (positive_update d i hd hb)).1 _ |>.mp hc
  rw [eval_QP,resOf_zero 𝓡 _ hn (positive_update d i hd (by omega : 0 < a+b)) _
    (fun j => (combined_hom d i a b j).map (eval c))]
  refine ⟨x,hx,?_⟩
  intro j
  by_cases hj : j = i
  · subst j
    simp only [combined,if_pos rfl,ite_true,map_mul,eval_H,hf,mul_zero]
  · rw [combined,if_neg hj,← HG_other d i a b j hj,eval_H]
    exact hf j

noncomputable def diag {m : ℕ} (e : Fin m → ℕ) (v : CoeffVar e) : ℂ :=
  if v.2.1 = Finsupp.single v.1 (e v.1) then 1 else 0

lemma eval_diag (𝓡 : ResultantSystem) {m : ℕ} (hm : 1 ≤ m) (e : Fin m → ℕ)
    (he : ∀ j,0 < e j) : eval (diag e) (map (Int.castRingHom ℂ) (𝓡.res e)) = 1 := by
  classical
  change eval (fun v : CoeffVar e => if v.2.1 = Finsupp.single v.1 (e v.1) then (1 : ℂ) else 0)
    (map (Int.castRingHom ℂ) (𝓡.res e)) = 1
  have h := congrArg (Int.castRingHom ℂ) ((𝓡.spec e hm he).2.1)
  rw [map_eval] at h
  simpa [diag,Function.comp_def] using h

lemma form_diag {m : ℕ} (e : Fin m → ℕ) (j : Fin m) :
    form e (diag e) j = X j ^ e j := by
  change form e (fun v : CoeffVar e => if v.2.1 = Finsupp.single v.1 (e v.1) then (1 : ℂ) else 0) j = _
  have h := form_coeff e (fun j => (X j ^ e j : MvPolynomial (Fin m) ℂ))
    (fun j => isHomogeneous_X_pow j (e j)) j
  simpa [diag,X_pow_eq_monomial,coeff_monomial,eq_comm] using h

noncomputable def point (z : ℂ) : Vars d i a b → ℂ :=
  Sum.elim (fun v => (if v.1 = i then z else 1) * diag (Function.update d i a) v)
    (diag (Function.update d i b))

lemma point_H (z : ℂ) : point d i a b z ∘ embedH d i a b = diag (Function.update d i b) := by
  classical
  funext v
  by_cases hv : v.1 = i
  · simp [Function.comp_def,point,embedH,hv]
  · simp [Function.comp_def,point,embedH,hv,diag,Function.update_of_ne hv]

lemma point_G : point d i a b 1 ∘ Sum.inl = diag (Function.update d i a) := by
  classical
  funext v
  simp [point,Function.comp_def]

lemma eval_HP_point (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (hb : 0 < b) (z : ℂ) :
    eval (point d i a b z) (HP d i a b 𝓡) = 1 := by
  rw [HP,eval_rename,point_H]
  exact eval_diag 𝓡 hn _ (positive_update d i hd hb)

lemma eval_RP_one (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) :
    eval (point d i a b 1) (RP d i a b 𝓡) = 1 := by
  rw [RP,eval_rename,point_G]
  exact eval_diag 𝓡 hn _ (positive_update d i hd ha)

lemma eval_RP_zero (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) :
    eval (point d i a b 0) (RP d i a b 𝓡) = 0 := by
  classical
  rw [RP,eval_rename]
  have hfun : point d i a b 0 ∘ Sum.inl =
      fun v : CoeffVar (Function.update d i a) =>
        if v.1 = i then 0 * diag (Function.update d i a) v else diag (Function.update d i a) v := by
    funext v
    by_cases hv : v.1 = i <;> simp [point,Function.comp_def,hv]
  rw [hfun,(lemma_2_2 𝓡 hn _ (positive_update d i hd ha)).2.1]
  have hpos : 0 < ∏ j ∈ univ.erase i, Function.update d i a j :=
    prod_pos (fun j hj => positive_update d i hd ha j)
  rw [zero_pow (Nat.ne_of_gt hpos),zero_mul]

lemma RP_not_dvd_HP (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) (hb : 0 < b) :
    ¬ RP d i a b 𝓡 ∣ HP d i a b 𝓡 := by
  rintro ⟨A,hA⟩
  have h := congrArg (eval (point d i a b 0)) hA
  rw [map_mul,eval_RP_zero d i a b 𝓡 hn hd ha,eval_HP_point d i a b 𝓡 hn hd hb,zero_mul] at h
  exact one_ne_zero h

lemma eval_QP_one (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) (hb : 0 < b) :
    eval (point d i a b 1) (QP d i a b 𝓡) = 1 := by
  classical
  rw [eval_QP]
  have hforms : (fun j => map (eval (point d i a b 1)) (combined d i a b j)) =
      fun j => X j ^ Function.update d i (a+b) j := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [combined,if_pos rfl,ite_true,map_mul,eval_G,eval_H,point_G,point_H,form_diag,
        Function.update_self,pow_add]
    · simp only [combined,if_neg hj,eval_G,point_G,form_diag,Function.update_of_ne hj]
  rw [hforms]
  unfold resOf
  have hcoeff : (fun v : CoeffVar (Function.update d i (a+b)) =>
      (X v.1 ^ Function.update d i (a+b) v.1 : MvPolynomial (Fin n) ℂ).coeff v.2.1) =
      diag (Function.update d i (a+b)) := by
    funext v
    simp [diag,X_pow_eq_monomial,coeff_monomial,eq_comm]
  rw [hcoeff]
  exact eval_diag 𝓡 hn _ (positive_update d i hd (by omega : 0 < a+b))

lemma coeffHom_G (j : Fin n) : CoeffHom (G d i a b j) 1 := by
  intro e
  rw [G,coeff_map]
  exact (generic_coeff_homogeneous _ j e).rename_isHomogeneous

lemma coeffHom_H (j : Fin n) : CoeffHom (H d i a b j) 1 := by
  intro e
  rw [H,coeff_map]
  exact (generic_coeff_homogeneous _ j e).rename_isHomogeneous

lemma QP_hom (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) (hb : 0 < b) :
    (QP d i a b 𝓡).IsHomogeneous
      ((∑ j,∏ k ∈ univ.erase j,Function.update d i a k) +
       (∑ j,∏ k ∈ univ.erase j,Function.update d i b k)) := by
  classical
  have hcoeff (j : Fin n) : CoeffHom (combined d i a b j) (if j = i then 2 else 1) := by
    by_cases hj : j = i
    · subst j
      simpa only [combined,if_pos rfl,ite_true] using coeffHom_mul (coeffHom_G d i a b i) (coeffHom_H d i a b i)
    · simpa only [combined,if_neg hj] using coeffHom_G d i a b j
  have h := homogeneous_aeval (block_weighted 𝓡 hn (Function.update d i (a+b))
    (positive_update d i hd (by omega : 0 < a+b)) (fun j => if j = i then 2 else 1))
    (fun v : CoeffVar (Function.update d i (a+b)) => (combined d i a b v.1).coeff v.2.1)
    (fun v => hcoeff v.1 v.2.1)
  have heq : (∑ j, (if j = i then 2 else 1) * ∏ k ∈ univ.erase j,Function.update d i (a+b) k) =
      ((∑ j,∏ k ∈ univ.erase j,Function.update d i a k) +
       (∑ j,∏ k ∈ univ.erase j,Function.update d i b k)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · subst j
      simp only [ite_true,prod_update_of_notMem (notMem_erase i univ),two_mul]
    · have hij : i ∈ univ.erase j := by simp [Ne.symm hji]
      simp only [if_neg hji,one_mul,prod_update_of_mem hij,add_mul]
  simpa only [heq,QP] using h

lemma RP_hom (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) :
    (RP d i a b 𝓡).IsHomogeneous (∑ j,∏ k ∈ univ.erase j,Function.update d i a k) :=
  (((lemma_2_2 𝓡 hn _ (positive_update d i hd ha)).2.2.1).map (Int.castRingHom ℂ)).rename_isHomogeneous

lemma HP_hom (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (hb : 0 < b) :
    (HP d i a b 𝓡).IsHomogeneous (∑ j,∏ k ∈ univ.erase j,Function.update d i b k) :=
  (((lemma_2_2 𝓡 hn _ (positive_update d i hd hb)).2.2.1).map (Int.castRingHom ℂ)).rename_isHomogeneous

lemma polynomial_identity (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (hd : ∀ j,j ≠ i → 0 < d j) (ha : 0 < a) (hb : 0 < b) :
    QP d i a b 𝓡 = RP d i a b 𝓡 * HP d i a b 𝓡 := by
  classical
  have hR := RP_prime d i a b 𝓡 hn hd ha
  have hH := HP_prime d i a b 𝓡 hn hd hb
  obtain ⟨A,hA⟩ := HP_dvd d i a b 𝓡 hn hd ha hb
  have hdiv : RP d i a b 𝓡 ∣ A := by
    have h := RP_dvd d i a b 𝓡 hn hd ha hb
    rw [hA] at h
    exact (hR.dvd_mul.mp h).resolve_left (RP_not_dvd_HP d i a b 𝓡 hn hd ha hb)
  obtain ⟨B,hB⟩ := hdiv
  have hQ : QP d i a b 𝓡 = (RP d i a b 𝓡 * HP d i a b 𝓡) * B := by
    rw [hA,hB]
    ring
  have hQ0 : QP d i a b 𝓡 ≠ 0 := by
    intro h
    have he := eval_QP_one d i a b 𝓡 hn hd ha hb
    simp [h] at he
  have hB0 : B ≠ 0 := by intro h; simp [h] at hQ; exact hQ0 hQ
  have hprod0 : RP d i a b 𝓡 * HP d i a b 𝓡 ≠ 0 := mul_ne_zero hR.ne_zero hH.ne_zero
  have hdeg := congrArg totalDegree hQ
  rw [(QP_hom d i a b 𝓡 hn hd ha hb).totalDegree hQ0,
    totalDegree_mul_of_isDomain hprod0 hB0,
    ((RP_hom d i a b 𝓡 hn hd ha).mul (HP_hom d i a b 𝓡 hn hd hb)).totalDegree hprod0] at hdeg
  have hBd : B.totalDegree = 0 := by omega
  have hBC := totalDegree_eq_zero_iff_eq_C.mp hBd
  have he := congrArg (eval (point d i a b 1)) hQ
  rw [eval_QP_one d i a b 𝓡 hn hd ha hb,map_mul,map_mul,
    eval_RP_one d i a b 𝓡 hn hd ha,eval_HP_point d i a b 𝓡 hn hd hb,one_mul] at he
  have hB1 : B = 1 := by
    rw [hBC]
    rw [hBC,eval_C,one_mul] at he
    rw [← he,map_one]
  simpa only [hB1,mul_one] using hQ

end ResultantMultiplicativity

open ResultantMultiplicativity in
theorem solution (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ) (i : Fin n)
    (hd : ∀ j, j ≠ i → 0 < d j) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ j, j ≠ i → (f j).IsHomogeneous (d j))
    (g h : MvPolynomial (Fin n) ℂ) (hg : g.IsHomogeneous a) (hh : h.IsHomogeneous b) :
    resOf 𝓡 (Function.update d i (a + b)) (Function.update f i (g * h)) =
      resOf 𝓡 (Function.update d i a) (Function.update f i g) *
        resOf 𝓡 (Function.update d i b) (Function.update f i h) := by
  classical
  let fa := Function.update f i g
  let fb := Function.update f i h
  let u : Vars d i a b → ℂ := Sum.elim (fun v => (fa v.1).coeff v.2.1)
    (fun v => (fb v.1).coeff v.2.1)
  have hfa (j : Fin n) : (fa j).IsHomogeneous (Function.update d i a j) := by
    by_cases hj : j = i
    · simpa [fa,hj] using hg
    · simpa only [fa,Function.update_of_ne hj] using hf j hj
  have hfb (j : Fin n) : (fb j).IsHomogeneous (Function.update d i b j) := by
    by_cases hj : j = i
    · simpa [fb,hj] using hh
    · simpa only [fb,Function.update_of_ne hj] using hf j hj
  have huH : u ∘ embedH d i a b = fun v : CoeffVar (Function.update d i b) => (fb v.1).coeff v.2.1 := by
    funext v
    by_cases hv : v.1 = i
    · simp [u,Function.comp_def,embedH,hv]
    · simp [u,Function.comp_def,embedH,hv,fa,fb,Function.update_of_ne hv]
  have huG : u ∘ Sum.inl = fun v : CoeffVar (Function.update d i a) => (fa v.1).coeff v.2.1 := rfl
  have hG (j : Fin n) : map (eval u) (G d i a b j) = fa j := by
    rw [eval_G,huG,form_coeff _ fa hfa]
  have hH (j : Fin n) : map (eval u) (H d i a b j) = fb j := by
    rw [eval_H,huH,form_coeff _ fb hfb]
  have hcombined : (fun j => map (eval u) (combined d i a b j)) = Function.update f i (g*h) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [combined,ite_true,map_mul,hG,hH,fa,fb,Function.update_self]
    · simp only [combined,if_neg hj,hG,fa,Function.update_of_ne hj]
  have result := congrArg (eval u) (polynomial_identity d i a b 𝓡 hn hd ha hb)
  rw [eval_QP,hcombined,map_mul,RP,HP,eval_rename,eval_rename,huG,huH] at result
  exact result

#print axioms solution
