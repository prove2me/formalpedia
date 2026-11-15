-- Prove2me | solution 1 for ResultantVNP.lemma_2_6_6
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T11:14:24.392812+00:00
-- url     : https://prove2.me/submissions/e1045202-2773-4c2a-87f1-e082b4ba85e3

import Mathlib
import Definitions.Def_ResultantVNP_resOf

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace ResultantEvaluation
open MvPolynomial ResultantVNP
open scoped Matrix

private def degrees (n e : ℕ) : Fin (n+1) → ℕ :=
  Fin.lastCases (motive := fun _ => ℕ) e (fun _ => 1)

private abbrev HExp (n e : ℕ) := {v : Fin (n+1) →₀ ℕ // ∑ j, v j = e}

private noncomputable def lVar (n e : ℕ) (i : Fin n) (j : Fin (n+1)) :
    CoeffVar (degrees n e) :=
  ⟨i.castSucc, ⟨Finsupp.single j 1, by simp [degrees]⟩⟩

private noncomputable def hVar (n e : ℕ) (v : HExp n e) : CoeffVar (degrees n e) :=
  ⟨Fin.last n, ⟨v.1, by simpa [degrees] using v.2⟩⟩

private lemma single_injective {n : ℕ} {i j : Fin n}
    (h : (Finsupp.single i 1 : Fin n →₀ ℕ) = Finsupp.single j 1) : i = j := by
  classical
  by_contra hne
  have hh := congrArg (fun e => e i) h
  simp [Finsupp.single_apply, hne, Ne.symm hne] at hh

private lemma single_eq_iff {n : ℕ} (i j : Fin n) :
    (Finsupp.single i 1 : Fin n →₀ ℕ) = Finsupp.single j 1 ↔ i = j :=
  ⟨single_injective, fun h => by rw [h]⟩

private lemma lVar_inj {n e : ℕ} {i k : Fin n} {j l : Fin (n+1)} :
    lVar n e i j = lVar n e k l ↔ i = k ∧ j = l := by
  constructor
  · intro h
    exact ⟨Fin.castSucc_injective n (congrArg Sigma.fst h),
      single_injective (congrArg (fun v : CoeffVar (degrees n e) => v.2.1) h)⟩
  · rintro ⟨rfl,rfl⟩; rfl

private lemma hVar_inj {n e : ℕ} {v w : HExp n e} : hVar n e v = hVar n e w ↔ v = w := by
  constructor
  · intro h
    exact Subtype.ext (congrArg (fun v : CoeffVar (degrees n e) => v.2.1) h)
  · rintro rfl; rfl

private lemma lVar_ne_hVar {n e : ℕ} (i : Fin n) (j : Fin (n+1)) (v : HExp n e) :
    lVar n e i j ≠ hVar n e v := by
  intro h
  exact Fin.castSucc_ne_last i (congrArg Sigma.fst h)

private lemma coeff_cases {n e : ℕ} (v : CoeffVar (degrees n e)) :
    (∃ i j, v = lVar n e i j) ∨ ∃ w, v = hVar n e w := by
  obtain ⟨i,v,hv⟩ := v
  refine Fin.lastCases ?_ (fun i => ?_) i v hv
  · intro v hv
    exact Or.inr ⟨⟨v,by simpa [degrees] using hv⟩, rfl⟩
  · intro v hv
    have h1 : v.degree = 1 := by
      rw [Finsupp.degree_eq_sum]
      simpa [degrees] using hv
    obtain ⟨j,hj⟩ := (Finsupp.sum_eq_one_iff v).mp h1
    subst v
    exact Or.inl ⟨i,j,rfl⟩

private noncomputable def coeffMap (n e : ℕ) :
    (Fin n × Fin (n+1)) ⊕ HExp n e → CoeffVar (degrees n e) :=
  Sum.elim (fun ij => lVar n e ij.1 ij.2) (hVar n e)

private lemma coeffMap_bijective (n e : ℕ) : Function.Bijective (coeffMap n e) := by
  constructor
  · intro x y h
    cases x with
    | inl ij =>
      cases y with
      | inl kl =>
        have hh := lVar_inj.mp h
        simp [Prod.ext hh.1 hh.2]
      | inr w => exact False.elim (lVar_ne_hVar ij.1 ij.2 w h)
    | inr v =>
      cases y with
      | inl kl => exact False.elim (lVar_ne_hVar kl.1 kl.2 v h.symm)
      | inr w => simp [hVar_inj.mp h]
  · intro v
    rcases coeff_cases v with ⟨i,j,rfl⟩ | ⟨w,rfl⟩
    · exact ⟨Sum.inl (i,j),rfl⟩
    · exact ⟨Sum.inr w,rfl⟩

private noncomputable def coeffEquiv (n e : ℕ) :
    (Fin n × Fin (n+1)) ⊕ HExp n e ≃ CoeffVar (degrees n e) :=
  Equiv.ofBijective (coeffMap n e) (coeffMap_bijective n e)

private noncomputable def pack {S : Type} (n e : ℕ)
    (K : Fin n → Fin (n+1) → S) (w : HExp n e → S) : CoeffVar (degrees n e) → S :=
  fun v => Sum.elim (fun ij => K ij.1 ij.2) w ((coeffEquiv n e).symm v)

private lemma pack_lVar {S : Type} (n e : ℕ)
    (K : Fin n → Fin (n+1) → S) (w : HExp n e → S) (i : Fin n) (j : Fin (n+1)) :
    pack n e K w (lVar n e i j) = K i j := by
  change Sum.elim _ _ ((coeffEquiv n e).symm ((coeffEquiv n e) (.inl (i,j)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private lemma pack_hVar {S : Type} (n e : ℕ)
    (K : Fin n → Fin (n+1) → S) (w : HExp n e → S) (v : HExp n e) :
    pack n e K w (hVar n e v) = w v := by
  change Sum.elim _ _ ((coeffEquiv n e).symm ((coeffEquiv n e) (.inr v))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private noncomputable def exponentEquiv (n : ℕ) :
    Fin n ≃ {v : Fin n →₀ ℕ // ∑ j, v j = 1} :=
  Equiv.ofBijective (fun j => ⟨Finsupp.single j 1, by simp⟩) ⟨by
    intro i j h
    exact single_injective (congrArg Subtype.val h), by
    intro v
    have h1 : v.1.degree = 1 := by rw [Finsupp.degree_eq_sum]; exact v.2
    obtain ⟨j,hj⟩ := (Finsupp.sum_eq_one_iff v.1).mp h1
    exact ⟨j,Subtype.ext hj.symm⟩⟩

private lemma form_linear {n e : ℕ} (a : CoeffVar (degrees n e) → ℂ) (i : Fin n) :
    form (degrees n e) a i.castSucc = ∑ j : Fin (n+1), C (a (lVar n e i j)) * X j := by
  classical
  let E : Fin (n+1) ≃ {v : Fin (n+1) →₀ ℕ // ∑ j, v j = degrees n e i.castSucc} :=
    (exponentEquiv (n+1)).trans ((Equiv.refl _).subtypeEquiv (by
      intro v; simp [degrees]))
  unfold form
  symm
  apply Fintype.sum_equiv E
  intro j
  change C (a (lVar n e i j)) * X j =
    monomial (Finsupp.single j 1) (a (lVar n e i j))
  simp [X,C_mul_monomial]

private lemma eval_form_last {n e : ℕ} (a : CoeffVar (degrees n e) → ℂ)
    (x : Fin (n+1) → ℂ) :
    eval x (form (degrees n e) a (Fin.last n)) =
      ∑ v : HExp n e, a (hVar n e v) * ∏ j, x j ^ v.1 j := by
  classical
  let E : HExp n e ≃ {v : Fin (n+1) →₀ ℕ // ∑ j, v j = degrees n e (Fin.last n)} :=
    (Equiv.refl _).subtypeEquiv (by intro v; simp [degrees])
  unfold form
  simp only [map_sum,eval_monomial]
  symm
  apply Fintype.sum_equiv E
  intro v
  change a (hVar n e v) * (∏ j, x j ^ v.1 j) =
    a (hVar n e v) * v.1.prod (fun j k => x j ^ k)
  rw [Finsupp.prod_fintype _ _ (by simp)]

private lemma dvd_of_zeros {ι : Type} [Finite ι]
    {P Q : MvPolynomial ι ℂ} (hP : Irreducible P)
    (hz : ∀ x : ι → ℂ, eval x P = 0 → eval x Q = 0) : P ∣ Q := by
  let I : Ideal (MvPolynomial ι ℂ) := Ideal.span {P}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hP.prime
  have hmem : Q ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    intro x hx
    rw [aeval_eq_eval]
    apply hz
    have hp := hx P (Ideal.subset_span (by simp : P ∈ ({P} : Set _)))
    simpa only [aeval_eq_eval] using hp
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmem
  exact Ideal.mem_span_singleton.mp hmem


private def mat {n : ℕ} {S : Type} (K : Fin n → Fin (n+1) → S) : Matrix (Fin n) (Fin n) S :=
  fun i j => K i j.castSucc

private def tailcol {n : ℕ} {S : Type} (K : Fin n → Fin (n+1) → S) : Fin n → S :=
  fun i => K i (Fin.last n)

private noncomputable def kernelPoint {n : ℕ} {S : Type} [CommRing S]
    (K : Fin n → Fin (n+1) → S) : Fin (n+1) → S :=
  Fin.lastCases (mat K).det (fun i => -((mat K).adjugate *ᵥ tailcol K) i)

private lemma kernelPoint_map {n : ℕ} {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (K : Fin n → Fin (n+1) → S) :
    (fun j => φ (kernelPoint K j)) = kernelPoint (fun i j => φ (K i j)) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [kernelPoint,Fin.lastCases_last]
    exact φ.map_det (mat K)
  · simp only [kernelPoint,Fin.lastCases_castSucc,map_neg]
    congr 1
    have hm := RingHom.map_mulVec φ (mat K).adjugate (tailcol K) i
    have ha := φ.map_adjugate (mat K)
    change (mat K).adjugate.map φ = (mat (fun i j => φ (K i j))).adjugate at ha
    rw [ha] at hm
    exact hm

private lemma eval_form_scaled {n e : ℕ} (a : CoeffVar (degrees n e) → ℂ)
    (x : Fin (n+1) → ℂ) (t : ℂ) :
    eval (fun j => t*x j) (form (degrees n e) a (Fin.last n)) =
      t^e * eval x (form (degrees n e) a (Fin.last n)) := by
  classical
  rw [eval_form_last,eval_form_last,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,v.2]
  ring

private lemma kernelPoint_of_root {n : ℕ} (K : Fin n → Fin (n+1) → ℂ)
    (hdet : (mat K).det ≠ 0) (x : Fin (n+1) → ℂ) (hx : x ≠ 0)
    (hlin : ∀ i, ∑ j, K i j * x j = 0) :
    ∃ t : ℂ, kernelPoint K = fun j => t*x j := by
  let v : Fin n → ℂ := fun i => x i.castSucc
  let z := x (Fin.last n)
  have hAv : mat K *ᵥ v = -(z • tailcol K) := by
    ext i
    have hi := hlin i
    rw [Fin.sum_univ_castSucc] at hi
    change (∑ j : Fin n, K i j.castSucc * x j.castSucc) = -(z * K i (Fin.last n))
    dsimp [z]
    linear_combination hi
  have hz : z ≠ 0 := by
    intro hz
    have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet (by simpa [hz] using hAv)
    apply hx
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hz
    · exact congrFun hv0 i
  have hmul := congrArg (fun w => (mat K).adjugate *ᵥ w) hAv
  rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,
    Matrix.mulVec_neg,Matrix.mulVec_smul] at hmul
  refine ⟨(mat K).det/z, ?_⟩
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [kernelPoint,Fin.lastCases_last]
    exact (div_mul_cancel₀ _ hz).symm
  · simp only [kernelPoint,Fin.lastCases_castSucc]
    have hi := congrFun hmul i
    simp only [Pi.smul_apply,smul_eq_mul,Pi.neg_apply] at hi
    apply (mul_left_cancel₀ hz)
    dsimp [v] at hi
    calc
      z * -((mat K).adjugate *ᵥ tailcol K) i = (mat K).det * x i.castSucc := by
        linear_combination -hi
      _ = z * ((mat K).det / z * x i.castSucc) := by field_simp

private noncomputable def genericK (n e : ℕ) (i : Fin n) (j : Fin (n+1)) :
    MvPolynomial (CoeffVar (degrees n e)) ℂ := X (lVar n e i j)

private noncomputable def eliminant (n e : ℕ) : MvPolynomial (CoeffVar (degrees n e)) ℂ :=
  (mat (genericK n e)).det * ∑ v : HExp n e,
    X (hVar n e v) * ∏ j, kernelPoint (genericK n e) j ^ v.1 j

private lemma eliminant_map {n e : ℕ} {S : Type} [CommRing S]
    (φ : MvPolynomial (CoeffVar (degrees n e)) ℂ →+* S) :
    φ (eliminant n e) =
      (mat (fun i j => φ (X (lVar n e i j)))).det * ∑ v : HExp n e,
        φ (X (hVar n e v)) * ∏ j,
          kernelPoint (fun i j => φ (X (lVar n e i j))) j ^ v.1 j := by
  classical
  unfold eliminant
  simp only [map_mul,map_sum,map_prod,map_pow]
  rw [φ.map_det]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [congrFun (kernelPoint_map φ (genericK n e)) j]
  rfl

private lemma resultant_dvd_eliminant (𝓡 : ResultantSystem) (n e : ℕ) (he : 0 < e) :
    map (Int.castRingHom ℂ) (𝓡.res (degrees n e)) ∣ eliminant n e := by
  classical
  have hd : ∀ i, 0 < degrees n e i := by
    intro i
    exact Fin.lastCases (by simpa [degrees] using he) (fun _ => by simp [degrees]) i
  obtain ⟨hzero,_,hirr⟩ := 𝓡.spec (degrees n e) (by omega) hd
  apply dvd_of_zeros hirr
  intro a ha
  obtain ⟨x,hx,hf⟩ := (hzero a).mp ha
  rw [eliminant_map]
  simp only [eval_X]
  let K : Fin n → Fin (n+1) → ℂ := fun i j => a (lVar n e i j)
  change (mat K).det * (∑ v : HExp n e,
    a (hVar n e v) * ∏ j, kernelPoint K j ^ v.1 j) = 0
  by_cases hdet : (mat K).det = 0
  · simp [hdet]
  · have hlin : ∀ i, ∑ j, K i j * x j = 0 := by
      intro i
      have hi := hf i.castSucc
      rw [form_linear] at hi
      simpa [K,map_sum,map_mul] using hi
    obtain ⟨t,ht⟩ := kernelPoint_of_root K hdet x hx hlin
    rw [← eval_form_last,ht,eval_form_scaled,hf (Fin.last n),mul_zero,mul_zero]

private def affineK {n : ℕ} {S : Type} [Zero S] [One S] [DecidableEq (Fin n)]
    (c : Fin n → S) (i : Fin n) : Fin (n+1) → S :=
  Fin.lastCases (c i) (fun j => if i = j then 1 else 0)

private def point {n : ℕ} {S : Type} [Neg S] [One S] (c : Fin n → S) : Fin (n+1) → S :=
  Fin.lastCases 1 (fun i => -c i)

private lemma affineK_mat {n : ℕ} {S : Type} [CommRing S] (c : Fin n → S) :
    mat (affineK c) = (1 : Matrix (Fin n) (Fin n) S) := by
  ext i j
  simp [mat,affineK,Matrix.one_apply]

private lemma affineK_tail {n : ℕ} {S : Type} [CommRing S] (c : Fin n → S) :
    tailcol (affineK c) = c := by
  funext i
  simp [tailcol,affineK]

private lemma affineK_kernel {n : ℕ} {S : Type} [CommRing S] (c : Fin n → S) :
    kernelPoint (affineK c) = point c := by
  unfold kernelPoint point
  rw [affineK_mat,affineK_tail]
  simp

private lemma affineK_cast {n : ℕ} {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (c : Fin n → S) :
    (fun i j => φ (affineK c i j)) = affineK (fun i => φ (c i)) := by
  funext i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [affineK]
  · by_cases h : i = k <;> simp [affineK,h]

private lemma pack_map {S T : Type} (n e : ℕ) (φ : S → T)
    (K : Fin n → Fin (n+1) → S) (w : HExp n e → S) :
    (fun v => φ (pack n e K w v)) = pack n e (fun i j => φ (K i j)) (fun v => φ (w v)) := by
  funext v
  rcases coeff_cases v with ⟨i,j,rfl⟩ | ⟨w,rfl⟩
  · simp only [pack_lVar]
  · simp only [pack_hVar]

private noncomputable def specialize (n e : ℕ) (c : Fin n → ℂ) :
    MvPolynomial (CoeffVar (degrees n e)) ℂ →ₐ[ℂ] MvPolynomial (HExp n e) ℂ :=
  aeval (pack n e (affineK (fun i => C (c i))) X)

private noncomputable def linearEval (n e : ℕ) (c : Fin n → ℂ) : MvPolynomial (HExp n e) ℂ :=
  ∑ v : HExp n e, X v * C (∏ j, point c j ^ v.1 j)

private lemma specialize_eliminant (n e : ℕ) (c : Fin n → ℂ) :
    specialize n e c (eliminant n e) = linearEval n e c := by
  classical
  rw [show specialize n e c (eliminant n e) =
    (specialize n e c).toRingHom (eliminant n e) from rfl,eliminant_map]
  simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,specialize,aeval_X,pack_lVar,pack_hVar,
    affineK_mat,Matrix.det_one,one_mul,affineK_kernel]
  unfold linearEval
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [map_pow]
  congr 1
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [point]

private lemma eval_linearEval (n e : ℕ) (c : Fin n → ℂ) (w : HExp n e → ℂ) :
    eval w (linearEval n e c) = ∑ v : HExp n e, w v * ∏ j, point c j ^ v.1 j := by
  simp [linearEval,map_sum,map_mul]

private lemma degree_linearEval (n e : ℕ) (c : Fin n → ℂ) :
    (linearEval n e c).totalDegree ≤ 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro v hv
  simpa only [totalDegree_X,totalDegree_C,add_zero] using totalDegree_mul (X v : MvPolynomial (HExp n e) ℂ)
    (C (∏ j, point c j ^ v.1 j))

private noncomputable def zExp (n e : ℕ) : HExp n e :=
  ⟨Finsupp.single (Fin.last n) e, by simp⟩

private noncomputable def zCoeff (n e : ℕ) (v : HExp n e) : ℂ :=
  if v = zExp n e then 1 else 0

private lemma eval_linearEval_z (n e : ℕ) (c : Fin n → ℂ) :
    eval (zCoeff n e) (linearEval n e c) = 1 := by
  classical
  rw [eval_linearEval]
  simp only [zCoeff,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∏ j, point c j ^ (Finsupp.single (Fin.last n) e) j) = 1
  rw [← Finsupp.prod_fintype _ _ (by simp),Finsupp.prod_single_index (by simp)]
  simp [point]

private lemma linearEval_irreducible (n e : ℕ) (c : Fin n → ℂ) :
    Irreducible (linearEval n e c) := by
  apply irreducible_of_totalDegree_eq_one
  · have hd := degree_linearEval n e c
    have hpos : (linearEval n e c).totalDegree ≠ 0 := by
      intro hz
      have hC := totalDegree_eq_zero_iff_eq_C.mp hz
      have hzero : eval (fun _ => (0 : ℂ)) (linearEval n e c) = 0 := by
        rw [eval_linearEval]
        simp only [zero_mul,Finset.sum_const_zero]
      have hone := eval_linearEval_z n e c
      rw [hC,eval_C] at hzero hone
      exact zero_ne_one (hzero.symm.trans hone)
    omega
  · intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hx0
    have hL : linearEval n e c = 0 := by
      ext v
      have hh := hx v
      simpa [hx0] using hh
    have hone := eval_linearEval_z n e c
    rw [hL,map_zero] at hone
    exact zero_ne_one hone

private lemma eval_pack {ι : Type} (n e : ℕ)
    (K : Fin n → Fin (n+1) → MvPolynomial ι ℂ) (w : HExp n e → MvPolynomial ι ℂ)
    (p : MvPolynomial (CoeffVar (degrees n e)) ℂ) (c : ι → ℂ) :
    eval c (aeval (pack n e K w) p) =
      eval (pack n e (fun i j => eval c (K i j)) (fun v => eval c (w v))) p := by
  change aeval c (aeval (pack n e K w) p) =
    aeval (pack n e (fun i j => eval c (K i j)) (fun v => eval c (w v))) p
  rw [comp_aeval_apply]
  change aeval (fun v => eval c (pack n e K w v)) p = _
  rw [pack_map]

private lemma eval_specialize (n e : ℕ) (c : Fin n → ℂ)
    (p : MvPolynomial (CoeffVar (degrees n e)) ℂ) (w : HExp n e → ℂ) :
    eval w (specialize n e c p) = eval (pack n e (affineK c) w) p := by
  unfold specialize
  rw [eval_pack,affineK_cast]
  simp only [eval_C,eval_X]

private noncomputable def normPoly (𝓡 : ResultantSystem) (n e : ℕ) : MvPolynomial (Fin n) ℂ :=
  aeval (pack n e (affineK X) (fun v => C (zCoeff n e v)))
    (map (Int.castRingHom ℂ) (𝓡.res (degrees n e)))

private lemma eval_normPoly (𝓡 : ResultantSystem) (n e : ℕ) (c : Fin n → ℂ) :
    eval c (normPoly 𝓡 n e) = eval (pack n e (affineK c) (zCoeff n e))
      (map (Int.castRingHom ℂ) (𝓡.res (degrees n e))) := by
  unfold normPoly
  rw [eval_pack,affineK_cast]
  simp only [eval_C,eval_X]

private lemma eval_affine_form (n e : ℕ) (c : Fin n → ℂ) (w : HExp n e → ℂ)
    (x : Fin (n+1) → ℂ) (i : Fin n) :
    eval x (form (degrees n e) (pack n e (affineK c) w) i.castSucc) =
      x i.castSucc + c i * x (Fin.last n) := by
  classical
  rw [form_linear]
  simp only [map_sum,map_mul,eval_C,eval_X,pack_lVar]
  rw [Fin.sum_univ_castSucc]
  simp [affineK]

private lemma eval_z_form (n e : ℕ) (K : Fin n → Fin (n+1) → ℂ)
    (x : Fin (n+1) → ℂ) :
    eval x (form (degrees n e) (pack n e K (zCoeff n e)) (Fin.last n)) =
      x (Fin.last n)^e := by
  classical
  rw [eval_form_last]
  simp only [pack_hVar,zCoeff,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∏ j, x j ^ (Finsupp.single (Fin.last n) e) j) = _
  rw [← Finsupp.prod_fintype _ _ (by simp),Finsupp.prod_single_index (by simp)]

private lemma norm_nonzero (𝓡 : ResultantSystem) (n e : ℕ) (he : 0 < e) (c : Fin n → ℂ) :
    eval c (normPoly 𝓡 n e) ≠ 0 := by
  classical
  rw [eval_normPoly]
  intro h
  have hd : ∀ i, 0 < degrees n e i := fun i =>
    Fin.lastCases (by simpa [degrees] using he) (fun _ => by simp [degrees]) i
  obtain ⟨x,hx,hf⟩ := ((𝓡.spec (degrees n e) (by omega) hd).1 _).mp h
  have hz : x (Fin.last n) = 0 := by
    have hh := hf (Fin.last n)
    rw [eval_z_form] at hh
    exact (eq_zero_of_pow_eq_zero hh)
  apply hx
  funext j
  refine Fin.lastCases hz (fun i => ?_) j
  have hi := hf i.castSucc
  rw [eval_affine_form,hz,mul_zero,add_zero] at hi
  exact hi

private lemma polynomial_nonvanishing_constant {ι : Type} [Finite ι]
    (p : MvPolynomial ι ℂ) (hp : ∀ c : ι → ℂ, eval c p ≠ 0) :
    ∃ a : ℂ, p = C a := by
  let I : Ideal (MvPolynomial ι ℂ) := Ideal.span {p}
  have hz : zeroLocus ℂ I = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    exact hp c (by simpa only [aeval_eq_eval] using
      (hc p (Ideal.subset_span (by simp : p ∈ ({p} : Set _)))))
  have hrad := vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I
  rw [hz,vanishingIdeal_empty] at hrad
  have hI : I = ⊤ := Ideal.radical_eq_top.mp hrad.symm
  have hu : IsUnit p := Ideal.span_singleton_eq_top.mp hI
  obtain ⟨a,_,ha⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  exact ⟨a,ha⟩

private lemma norm_at_zero (𝓡 : ResultantSystem) (n e : ℕ) (he : 0 < e) :
    eval (fun _ => 0) (normPoly 𝓡 n e) = 1 := by
  classical
  rw [eval_normPoly]
  have hd : ∀ i, 0 < degrees n e i := fun i =>
    Fin.lastCases (by simpa [degrees] using he) (fun _ => by simp [degrees]) i
  have h := congrArg (Int.castRingHom ℂ) (𝓡.spec (degrees n e) (by omega) hd).2.1
  rw [map_eval] at h
  simp only [map_one] at h
  convert h using 1
  congr 2
  funext v
  rcases coeff_cases v with ⟨i,j,rfl⟩ | ⟨v,rfl⟩
  · rw [pack_lVar]
    simp only [Function.comp_def,Int.coe_castRingHom,lVar]
    simp only [degrees,Fin.lastCases_castSucc,single_eq_iff,apply_ite,Int.cast_one,Int.cast_zero]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [affineK, Ne.symm (Fin.castSucc_ne_last i)]
    · simp [affineK,eq_comm]
  · rw [pack_hVar]
    simp only [Function.comp_def,Int.coe_castRingHom,hVar]
    have hv : v = zExp n e ↔ v.1 = Finsupp.single (Fin.last n) e := Subtype.ext_iff
    simp [zCoeff,degrees,hv,apply_ite]

private lemma norm_eq_one (𝓡 : ResultantSystem) (n e : ℕ) (he : 0 < e) :
    normPoly 𝓡 n e = 1 := by
  obtain ⟨a,ha⟩ := polynomial_nonvanishing_constant _ (norm_nonzero 𝓡 n e he)
  have h := norm_at_zero 𝓡 n e he
  rw [ha,eval_C] at h
  simp [ha,h]

private lemma specialize_nonunit (𝓡 : ResultantSystem) (n e : ℕ) (he : 0 < e)
    (c : Fin n → ℂ) :
    ¬IsUnit (specialize n e c (map (Int.castRingHom ℂ) (𝓡.res (degrees n e)))) := by
  classical
  intro hu
  have hd : ∀ i, 0 < degrees n e i := fun i =>
    Fin.lastCases (by simpa [degrees] using he) (fun _ => by simp [degrees]) i
  have hzero : eval (fun _ => (0 : ℂ))
      (specialize n e c (map (Int.castRingHom ℂ) (𝓡.res (degrees n e)))) = 0 := by
    rw [eval_specialize]
    apply ((𝓡.spec (degrees n e) (by omega) hd).1 _).mpr
    refine ⟨point c, ?_, ?_⟩
    · intro hz
      have hh := congrFun hz (Fin.last n)
      simpa [point] using hh
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [eval_form_last]
        simp only [pack_hVar,zero_mul,Finset.sum_const_zero]
      · rw [eval_affine_form]
        simp [point]
  have hm := hu.map (eval (fun _ => (0 : ℂ)))
  rw [hzero] at hm
  exact not_isUnit_zero hm

private lemma specialize_eq_linearEval (𝓡 : ResultantSystem) (n e : ℕ) (he : 0 < e)
    (c : Fin n → ℂ) :
    specialize n e c (map (Int.castRingHom ℂ) (𝓡.res (degrees n e))) = linearEval n e c := by
  obtain ⟨U,hU⟩ := resultant_dvd_eliminant 𝓡 n e he
  have h := congrArg (specialize n e c) hU
  rw [specialize_eliminant,map_mul] at h
  have hunit : IsUnit (specialize n e c U) :=
    ((linearEval_irreducible n e c).isUnit_or_isUnit h).resolve_left
      (specialize_nonunit 𝓡 n e he c)
  obtain ⟨a,_,ha⟩ := isUnit_iff_eq_C_of_isReduced.mp hunit
  rw [ha] at h
  have hn : eval (zCoeff n e)
      (specialize n e c (map (Int.castRingHom ℂ) (𝓡.res (degrees n e)))) = 1 := by
    rw [eval_specialize,← eval_normPoly,norm_eq_one 𝓡 n e he,map_one]
  have hv := congrArg (eval (zCoeff n e)) h
  rw [eval_linearEval_z,map_mul,hn,eval_C,one_mul] at hv
  rw [← hv,map_one,mul_one] at h
  exact h.symm

private lemma homogeneous_expansion {n e : ℕ} (h : MvPolynomial (Fin (n+1)) ℂ)
    (hh : h.IsHomogeneous e) :
    h = ∑ v : HExp n e, monomial v.1 (h.coeff v.1) := by
  classical
  ext d
  rw [coeff_sum]
  by_cases hd : ∑ j, d j = e
  · rw [Finset.sum_eq_single (⟨d,hd⟩ : HExp n e)]
    · simp
    · intro v hv hne
      have hne' : v.1 ≠ d := fun heq => hne (Subtype.ext heq)
      simp [coeff_monomial,hne']
    · simp
  · have hzero : h.coeff d = 0 := hh.coeff_eq_zero (by
      simpa only [Finsupp.degree_eq_sum] using hd)
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro v hv
    have hne : v.1 ≠ d := by intro heq; exact hd (heq ▸ v.2)
    simp [coeff_monomial,hne]

private lemma eval_homogeneous {n e : ℕ} (h : MvPolynomial (Fin (n+1)) ℂ)
    (hh : h.IsHomogeneous e) (x : Fin (n+1) → ℂ) :
    eval x h = ∑ v : HExp n e, h.coeff v.1 * ∏ j, x j ^ v.1 j := by
  conv_lhs => rw [homogeneous_expansion h hh,map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [eval_monomial,Finsupp.prod_fintype _ _ (by simp)]

private lemma forms_coeff (n e : ℕ) (c : Fin n → ℂ)
    (h : MvPolynomial (Fin (n+1)) ℂ) :
    (fun v : CoeffVar (degrees n e) =>
      (Fin.lastCases (motive := fun _ => MvPolynomial (Fin (n+1)) ℂ) h
        (fun i => X i.castSucc + C (c i) * X (Fin.last n)) v.1).coeff v.2.1) =
      pack n e (affineK c) (fun v => h.coeff v.1) := by
  classical
  funext v
  rcases coeff_cases v with ⟨i,j,rfl⟩ | ⟨v,rfl⟩
  · rw [pack_lVar]
    simp only [lVar,Fin.lastCases_castSucc]
    simp only [coeff_add,coeff_C_mul,coeff_X,single_eq_iff]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [affineK, Ne.symm (Fin.castSucc_ne_last i)]
    · simp [affineK,eq_comm]
  · rw [pack_hVar]
    simp only [hVar,Fin.lastCases_last]

theorem evaluation (𝓡 : ResultantSystem) (n e : ℕ) (he : 0 < e) (c : Fin n → ℂ)
    (h : MvPolynomial (Fin (n+1)) ℂ) (hh : h.IsHomogeneous e) :
    resOf 𝓡 (degrees n e)
      (Fin.lastCases (motive := fun _ => MvPolynomial (Fin (n+1)) ℂ) h
        (fun i => X i.castSucc + C (c i) * X (Fin.last n))) = eval (point c) h := by
  unfold resOf
  rw [forms_coeff,← eval_specialize,specialize_eq_linearEval 𝓡 n e he,
    eval_linearEval,eval_homogeneous h hh]

end ResultantEvaluation

theorem solution (𝓡 : ResultantVNP.ResultantSystem) (n e : ℕ) (_hn : 1 ≤ n)
    (he : 0 < e) (c : Fin n → ℂ) (h : MvPolynomial (Fin (n+1)) ℂ)
    (hh : h.IsHomogeneous e) :
    ResultantVNP.resOf 𝓡 (Fin.lastCases (motive := fun _ => ℕ) e (fun _ => 1))
      (Fin.lastCases (motive := fun _ => MvPolynomial (Fin (n+1)) ℂ) h
        (fun i => MvPolynomial.X i.castSucc + MvPolynomial.C (c i) * MvPolynomial.X (Fin.last n))) =
      MvPolynomial.eval (Fin.lastCases (motive := fun _ => ℂ) 1 (fun i => -c i)) h :=
  ResultantEvaluation.evaluation 𝓡 n e he c h hh

#print axioms solution
