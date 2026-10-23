-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P27.covariant_replacement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:51:44.823357+00:00
-- url     : https://prove2.me/submissions/d065b78a-3ed7-4bcf-90ed-84859585f4ac

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

open MeasureTheory QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

noncomputable section
namespace X7E12
open QAlgorithms.Papers.Independent.Claimed50.P27
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable instance X7E12_cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

abbrev G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

instance X7E12_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

instance X7E12_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

def K {d : ℕ} (V W : Matrix (Fin d) (Fin d) ℂ) : Matrix (CombReg d) (CombReg d) ℂ :=
  Matrix.kronecker (Matrix.kronecker V V)
    (Matrix.kronecker (V.map conj) (Matrix.kronecker (W.map conj) (Matrix.kronecker W W)))

lemma X7E12_cov_eq {d : ℕ} (V W : G d) : covarianceAction V W = K V.val W.val := by
  ext ⟨⟨a1, a2⟩, a3, a4, a5, a6⟩ ⟨⟨b1, b2⟩, b3, b4, b5, b6⟩
  simp [K, covarianceAction, Matrix.kronecker_apply]
  ring

lemma X7E12_map_mul {d : ℕ} (V V' : Matrix (Fin d) (Fin d) ℂ) :
    (V * V').map conj = V.map conj * V'.map conj :=
  Matrix.map_mul (f := starRingEnd ℂ)

lemma X7E12_K_mul {d : ℕ} (V W V' W' : Matrix (Fin d) (Fin d) ℂ) :
    K V W * K V' W' = K (V * V') (W * W') := by
  simp only [K, Matrix.kronecker, ← Matrix.mul_kronecker_mul, X7E12_map_mul]

lemma X7E12_map_ct {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) :
    (V.map conj)ᴴ = (Vᴴ).map conj := by
  ext i j; simp [Matrix.conjTranspose_apply]

lemma X7E12_K_ct {d : ℕ} (V W : Matrix (Fin d) (Fin d) ℂ) :
    (K V W)ᴴ = K Vᴴ Wᴴ := by
  simp only [K, Matrix.kronecker, Matrix.conjTranspose_kronecker, X7E12_map_ct]

lemma X7E12_K_one {d : ℕ} : K (1 : Matrix (Fin d) (Fin d) ℂ) 1 = 1 := by
  simp [K, Matrix.one_kronecker_one]

lemma X7E12_unit_left {d : ℕ} (W : G d) : W.valᴴ * W.val = 1 := by
  have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma X7E12_unit_right {d : ℕ} (W : G d) : W.val * W.valᴴ = 1 := by
  have := W.2; rw [Matrix.mem_unitaryGroup_iff] at this; exact this

lemma X7E12_K_unit {d : ℕ} (V W : G d) : K V.val W.val * (K V.val W.val)ᴴ = 1 ∧
    (K V.val W.val)ᴴ * K V.val W.val = 1 := by
  rw [X7E12_K_ct, X7E12_K_mul, X7E12_K_mul, X7E12_unit_right, X7E12_unit_right,
    X7E12_unit_left, X7E12_unit_left, X7E12_K_one]
  exact ⟨rfl, rfl⟩

lemma X7E12_K_cont {d : ℕ} (f g : G d → Matrix (Fin d) (Fin d) ℂ) (hf : Continuous f)
    (hg : Continuous g) : Continuous fun V => K (f V) (g V) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  simp only [K, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply]
  have hf' : ∀ i j, Continuous fun V => f V i j := fun i j => hf.matrix_elem i j
  have hg' : ∀ i j, Continuous fun V => g V i j := fun i j => hg.matrix_elem i j
  fun_prop

lemma X7E12_val_cont {d : ℕ} : Continuous fun V : G d => V.val := continuous_subtype_val

lemma X7E12_int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma X7E12_entry {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm

lemma X7E12_int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

lemma X7E12_conj_comp {d : ℕ} (A B C D : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (CombReg d) (CombReg d) ℂ) :
    K A B * (K C D * X * (K C D)ᴴ) * (K A B)ᴴ = K (A*C) (B*D) * X * (K (A*C) (B*D))ᴴ := by
  rw [X7E12_K_ct, X7E12_K_ct, X7E12_K_ct, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    ← X7E12_K_mul, ← X7E12_K_mul]
  simp only [Matrix.mul_assoc]

/-- twirl over V (wires 0,1) -/
def TV {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) : Matrix (CombReg d) (CombReg d) ℂ :=
  ∫ V : G d, K V.val 1 * X * (K V.val 1)ᴴ ∂(Schur.unitaryHaar d)

def TW {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) : Matrix (CombReg d) (CombReg d) ℂ :=
  ∫ W : G d, K 1 W.val * X * (K 1 W.val)ᴴ ∂(Schur.unitaryHaar d)

lemma X7E12_TV_int {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) :
    Integrable (fun V : G d => K V.val 1 * X * (K V.val 1)ᴴ) (Schur.unitaryHaar d) := by
  have h := X7E12_K_cont (fun V : G d => V.val) (fun _ => 1) X7E12_val_cont continuous_const
  exact ((h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma X7E12_TW_int {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) :
    Integrable (fun W : G d => K 1 W.val * X * (K 1 W.val)ᴴ) (Schur.unitaryHaar d) := by
  have h := X7E12_K_cont (fun _ => 1) (fun V : G d => V.val) continuous_const X7E12_val_cont
  exact ((h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma X7E12_TV_inv {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) (V : G d) :
    K V.val 1 * TV X * (K V.val 1)ᴴ = TV X := by
  unfold TV
  rw [← X7E12_int_conj _ _ _ (X7E12_TV_int X)]
  have h := integral_mul_left_eq_self (μ := Schur.unitaryHaar d)
    (fun U : G d => K U.val 1 * X * (K U.val 1)ᴴ) V
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [Submonoid.coe_mul]
  rw [X7E12_conj_comp, Matrix.mul_one]

lemma X7E12_TW_inv {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) (W : G d) :
    K 1 W.val * TW X * (K 1 W.val)ᴴ = TW X := by
  unfold TW
  rw [← X7E12_int_conj _ _ _ (X7E12_TW_int X)]
  have h := integral_mul_left_eq_self (μ := Schur.unitaryHaar d)
    (fun U : G d => K 1 U.val * X * (K 1 U.val)ᴴ) W
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [Submonoid.coe_mul]
  rw [X7E12_conj_comp, Matrix.mul_one]

lemma X7E12_TW_comm {d : ℕ} (Y : Matrix (CombReg d) (CombReg d) ℂ) (V : G d) :
    K V.val 1 * TW Y * (K V.val 1)ᴴ = TW (K V.val 1 * Y * (K V.val 1)ᴴ) := by
  unfold TW
  rw [← X7E12_int_conj _ _ _ (X7E12_TW_int Y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only
  rw [X7E12_conj_comp, X7E12_conj_comp]
  simp

def Sw {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) : Matrix (CombReg d) (CombReg d) ℂ := TW (TV R)

lemma X7E12_Sw_cov {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) : CloningCovariant (Sw R) := by
  intro V W _ _
  rw [X7E12_cov_eq]
  have hK : K V.val W.val = K 1 W.val * K V.val 1 := by rw [X7E12_K_mul]; simp
  have hinv : K V.val W.val * Sw R * (K V.val W.val)ᴴ = Sw R := by
    rw [hK, Matrix.conjTranspose_mul]
    unfold Sw
    have : K 1 W.val * K V.val 1 * TW (TV R) * ((K V.val 1)ᴴ * (K 1 W.val)ᴴ) =
        K 1 W.val * (K V.val 1 * TW (TV R) * (K V.val 1)ᴴ) * (K 1 W.val)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, X7E12_TW_comm, X7E12_TV_inv, X7E12_TW_inv]
  obtain ⟨_, h2⟩ := X7E12_K_unit V W
  calc Sw R * K V.val W.val = K V.val W.val * Sw R * ((K V.val W.val)ᴴ * K V.val W.val) := by
        conv_lhs => rw [← hinv]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_one]

def vv {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (y : CombReg d) : ℂ :=
  conj (U y.2.2.1 y.2.1) * (U y.2.2.2.1 y.1.1 * U y.2.2.2.2 y.1.2)

def om {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Matrix (CombReg d) (CombReg d) ℂ :=
  fun y x => vv U y * conj (vv U x)

def eC (d : ℕ) : (PairReg d × PairReg d) × (Fin d × Fin d) ≃ CombReg d where
  toFun p := (p.1.1, (p.2.1, (p.2.2, p.1.2)))
  invFun x := ((x.1, x.2.2.2), (x.2.1, x.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

lemma X7E12_sum_comb {d : ℕ} (F : CombReg d → CombReg d → ℂ) :
    ∑ x, ∑ y, F x y = ∑ a : PairReg d × PairReg d, ∑ b : PairReg d × PairReg d,
      ∑ i, ∑ j, ∑ k, ∑ l, F (a.1, (i, (k, a.2))) (b.1, (j, (l, b.2))) := by
  have h1 : ∑ x, ∑ y, F x y = ∑ p, ∑ q, F (eC d p) (eC d q) := by
    rw [← (eC d).sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← (eC d).sum_comp]
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  rfl

lemma X7E12_single_entry {m n p q : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) (a : n) (b : p) (k : m) (l : q) :
    (A * Matrix.single a b (1:ℂ) * B) k l = A k a * B b l := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul]
  simp [ite_and]

lemma X7E12_J {d : ℕ} (U : G d) (a b : PairReg d × PairReg d) :
    channelChoi (targetChannel U) b a =
      (U.val b.2.1 b.1.1 * U.val b.2.2 b.1.2) * conj (U.val a.2.1 a.1.1 * U.val a.2.2 a.1.2) := by
  simp only [channelChoi, targetChannel, conjSuperop, X7E12_single_entry,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, star_mul', map_mul, starRingEnd_apply]

lemma X7E12_point {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) (U : G d) :
    pointScore (insertedChoi X U) U = (X * om U.val).trace.re / (d : ℝ)^4 := by
  unfold pointScore
  congr 2
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.mul_apply, Matrix.diag_apply]
  rw [X7E12_sum_comb (fun x y => X x y * om U.val y x)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [X7E12_J, insertedChoi]
  simp only [Finset.sum_mul, om, vv]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, starRingEnd_self_apply]
  ring

lemma X7E12_fac {ι : Type*} [Fintype ι] (A B C : ι → ι → ℂ) :
    ∑ p, ∑ q, ∑ r, ∑ s, ∑ t, ∑ u, A s r * (B t p * C u q) =
      (∑ r, ∑ s, A s r) * ((∑ p, ∑ t, B t p) * (∑ q, ∑ u, C u q)) := by
  have h : ∀ p q, ∑ r, ∑ s, ∑ t, ∑ u, A s r * (B t p * C u q) =
      (∑ r, ∑ s, A s r) * ((∑ t, B t p) * (∑ u, C u q)) := by
    intro p q
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
  simp only [h]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]

lemma X7E12_key {d : ℕ} (U V W : Matrix (Fin d) (Fin d) ℂ) (y : CombReg d) :
    ∑ y', conj (K V W y' y) * vv U y' = vv (Wᴴ * U * V.map conj) y := by
  have hf := X7E12_fac (fun s r => W s y.2.2.1 * star (U s r) * V r y.2.1)
    (fun t p => star (W t y.2.2.2.1) * U t p * star (V p y.1.1))
    (fun u q => star (W u y.2.2.2.2) * U u q * star (V q y.1.2))
  simp only [Fintype.sum_prod_type, K, Matrix.kronecker, Matrix.kroneckerMap_apply, vv,
    Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_mul, map_sum,
    starRingEnd_apply, star_star]
  simp only [Finset.sum_mul] at hf ⊢
  convert hf using 1
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

lemma X7E12_om_conj {d : ℕ} (U V W : Matrix (Fin d) (Fin d) ℂ) :
    (K V W)ᴴ * om U * K V W = om (Wᴴ * U * V.map conj) := by
  ext y x
  simp only [om]
  rw [← X7E12_key, ← X7E12_key]
  simp only [om, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
    starRingEnd_self_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [starRingEnd_apply]
  ring

lemma X7E12_om_cont {d : ℕ} : Continuous fun U : G d => om U.val := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  simp only [om, vv]
  have h : ∀ i j, Continuous fun U : G d => U.val i j := fun i j => X7E12_val_cont.matrix_elem i j
  have h' : ∀ i j, Continuous fun U : G d => conj (U.val i j) := fun i j =>
    Complex.continuous_conj.comp (h i j)
  simp only [map_mul, starRingEnd_self_apply]
  exact ((h' _ _).mul ((h _ _).mul (h _ _))).mul ((h _ _).mul ((h' _ _).mul (h' _ _)))

def Om (d : ℕ) : Matrix (CombReg d) (CombReg d) ℂ := ∫ U : G d, om U.val ∂(Schur.unitaryHaar d)

lemma X7E12_mapRight (d : ℕ) (g : G d) :
    Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d) = QAlgorithms.Schur.unitaryHaar d := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    (Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d)) (QAlgorithms.Schur.unitaryHaar d)
  have hu : Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ]
    simp
  set c := Measure.haarScalarFactor (Measure.map (· * g) (QAlgorithms.Schur.unitaryHaar d))
      (QAlgorithms.Schur.unitaryHaar d) with hcdef
  have hc : c = 1 := by
    have := congrArg (fun m : Measure (G d) => m Set.univ) h
    simp only [Measure.smul_apply, measure_univ] at this
    rw [hu, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  rw [h, hc, one_smul]

lemma X7E12_intRight (d : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G d → E) (g : G d) :
    ∫ U, f (U * g) ∂(QAlgorithms.Schur.unitaryHaar d) = ∫ U, f U ∂(QAlgorithms.Schur.unitaryHaar d) := by
  have hm : MeasurableEmbedding (· * g : G d → G d) := (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← hm.integral_map, X7E12_mapRight]

lemma X7E12_bar_mem {d : ℕ} (V : G d) : V.val.map conj ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := X7E12_unit_right V
  have : star (V.val.map conj) = (V.val)ᵀ := by
    ext i j; simp [Matrix.star_apply]
  rw [this, show V.val.map conj = (V.val)ᴴᵀ from by ext i j; simp, ← Matrix.transpose_mul, h,
    Matrix.transpose_one]

lemma X7E12_Om_inv {d : ℕ} (V W : G d) :
    (K V.val W.val)ᴴ * Om d * K V.val W.val = Om d := by
  have hint : Integrable (fun U : G d => om U.val) (Schur.unitaryHaar d) :=
    X7E12_om_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold Om
  rw [← X7E12_int_conj _ _ _ hint]
  simp_rw [X7E12_om_conj]
  let Vb : G d := ⟨V.val.map conj, X7E12_bar_mem V⟩
  have h1 : ∀ U : G d, W.valᴴ * U.val * V.val.map conj = ((W⁻¹ * U) * Vb).val := by
    intro U
    rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.UnitaryGroup.inv_val]; rfl
  simp_rw [h1]
  have h2 := X7E12_intRight d (fun U : G d => om (W⁻¹ * U).val) Vb
  simp only [← mul_assoc] at h2
  rw [h2]
  exact integral_mul_left_eq_self (μ := Schur.unitaryHaar d) (fun U : G d => om U.val) W⁻¹

lemma X7E12_score_eq {d : ℕ} (X : Matrix (CombReg d) (CombReg d) ℂ) :
    combScore X = (X * Om d).trace.re / (d : ℝ)^4 := by
  have hint : Integrable (fun U : G d => X * om U.val * 1) (Schur.unitaryHaar d) :=
    ((continuous_const.matrix_mul X7E12_om_cont).matrix_mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun U : G d => (X * om U.val * 1).trace) (Schur.unitaryHaar d) :=
    (((continuous_const.matrix_mul X7E12_om_cont).matrix_mul continuous_const).matrix_trace).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold combScore
  simp_rw [X7E12_point]
  rw [integral_div]
  congr 1
  have h3 := X7E12_int_conj X 1 (fun U : G d => om U.val)
    (X7E12_om_cont.integrable_of_hasCompactSupport (μ := Schur.unitaryHaar d)
      (HasCompactSupport.of_compactSpace _))
  rw [Matrix.mul_one] at h3
  rw [← Om] at h3
  rw [← h3, ← X7E12_int_trace _ hint]
  have := integral_re hint2
  simp only [Matrix.mul_one, RCLike.re_to_complex] at this
  simp only [Matrix.mul_one]
  exact this

lemma X7E12_score_twirl {d : ℕ} (k : G d → Matrix (CombReg d) (CombReg d) ℂ)
    (hk : ∀ g, (k g)ᴴ * Om d * k g = Om d) (X : Matrix (CombReg d) (CombReg d) ℂ)
    (hc : Continuous k) :
    combScore (∫ g, k g * X * (k g)ᴴ ∂(Schur.unitaryHaar d)) = combScore X := by
  have hc1 : Continuous (fun g => k g * X * (k g)ᴴ) :=
    (hc.matrix_mul continuous_const).matrix_mul hc.matrix_conjTranspose
  have hint : Integrable (fun g => k g * X * (k g)ᴴ) (Schur.unitaryHaar d) :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [X7E12_score_eq, X7E12_score_eq]
  congr 2
  have h3 := X7E12_int_conj 1 (Om d) (fun g => k g * X * (k g)ᴴ) hint
  rw [Matrix.one_mul] at h3
  simp only [Matrix.one_mul] at h3
  rw [← h3, ← X7E12_int_trace]
  · have : ∀ g, (k g * X * (k g)ᴴ * Om d).trace = (X * Om d).trace := by
      intro g
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
        hk]
    simp [this]
  · exact (hc1.matrix_mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma X7E12_psd_int {d : ℕ} {m : Type*} [Fintype m] (F : G d → Matrix m m ℂ) (hF : Continuous F)
    (hp : ∀ g, (F g).PosSemidef) : (∫ g, F g ∂(Schur.unitaryHaar d)).PosSemidef := by
  have hint : Integrable F (Schur.unitaryHaar d) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, X7E12_entry _ hint, X7E12_entry _ hint]
    have h2 : (fun g => F g i j) = fun g => (starRingEnd ℂ) (F g j i) := by
      funext g
      have := (hp g).1
      have h3 := congrFun (congrFun this i) j
      rw [Matrix.conjTranspose_apply] at h3
      rw [← h3, starRingEnd_apply]
    rw [h2, integral_conj, starRingEnd_apply]
  · intro x
    let L0 : Matrix m m ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
        map_add' := fun M N => by simp [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec, dotProduct_smul] }
    let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L0
    have h1 : star x ⬝ᵥ ((∫ g, F g ∂(Schur.unitaryHaar d)) *ᵥ x) =
        ∫ g, star x ⬝ᵥ (F g *ᵥ x) ∂(Schur.unitaryHaar d) := (L.integral_comp_comm hint).symm
    have hre : ∀ g, star x ⬝ᵥ (F g *ᵥ x) = (((star x ⬝ᵥ (F g *ᵥ x)).re : ℝ) : ℂ) := by
      intro g
      have := Complex.nonneg_iff.mp ((hp g).dotProduct_mulVec_nonneg x)
      exact Complex.ext (by simp) (by simp [this.2])
    rw [h1, integral_congr_ae (Filter.Eventually.of_forall hre), integral_complex_ofReal]
    exact Complex.zero_le_real.mpr (integral_nonneg fun g =>
      (Complex.nonneg_iff.mp ((hp g).dotProduct_mulVec_nonneg x)).1)

def trR {α β : Type*} [Fintype β] (Y : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  fun p q => ∑ o, Y (p, o) (q, o)

lemma X7E12_sum_in4 {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (f : α → β → γ → δ → ε → ℂ) :
    ∑ o, ∑ a, ∑ b, ∑ c, ∑ e, f o a b c e = ∑ a, ∑ b, ∑ c, ∑ e, ∑ o, f o a b c e := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => ?_)
  exact Finset.sum_comm

lemma X7E12_trR_conj {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hN : Nᴴ * N = 1) (Y : Matrix (α × β) (α × β) ℂ) :
    trR (Matrix.kronecker M N * Y * (Matrix.kronecker M N)ᴴ) = M * trR Y * Mᴴ := by
  ext p q
  simp only [trR, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul, star_mul']
  rw [X7E12_sum_in4]
  have hN' : ∀ o1 o2 : β, ∑ o, star (N o o2) * N o o1 = if o2 = o1 then 1 else 0 := by
    intro o1 o2
    have := congrFun (congrFun hN o2) o1
    rw [Matrix.mul_apply] at this
    simpa [Matrix.one_apply, Matrix.conjTranspose_apply] using this
  have h1 : ∀ q1 o2 p1 o1, ∑ o, M p p1 * N o o1 * Y (p1, o1) (q1, o2) * (star (M q q1) * star (N o o2)) =
      M p p1 * Y (p1, o1) (q1, o2) * star (M q q1) * (if o2 = o1 then 1 else 0) := by
    intro q1 o2 p1 o1
    rw [← hN', Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun q1 _ => ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun p1 _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]

def e3 (d : ℕ) : ((PairReg d × Fin d) × Fin d) × PairReg d ≃ CombReg d where
  toFun x := (x.1.1.1, (x.1.1.2, (x.1.2, x.2)))
  invFun y := (((y.1, y.2.1), y.2.2.1), y.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def Bm {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) : Matrix (PairReg d × Fin d) (PairReg d × Fin d) ℂ :=
  Matrix.kronecker (Matrix.kronecker V V) (V.map conj)

lemma X7E12_K_sub {d : ℕ} (V W : Matrix (Fin d) (Fin d) ℂ) :
    (K V W).submatrix (e3 d) (e3 d) =
      Matrix.kronecker (Matrix.kronecker (Bm V) (W.map conj)) (Matrix.kronecker W W) := by
  ext x y
  simp only [K, Bm, e3, Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Equiv.coe_fn_mk]
  ring

lemma X7E12_sub_conj {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (M X : Matrix β β ℂ) :
    (M * X * Mᴴ).submatrix e e = M.submatrix e e * X.submatrix e e * (M.submatrix e e)ᴴ := by
  rw [← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e,
    Matrix.conjTranspose_submatrix]

lemma X7E12_bar_unit {d : ℕ} (V : G d) : (V.val.map conj)ᴴ * V.val.map conj = 1 ∧
    V.val.map conj * (V.val.map conj)ᴴ = 1 := by
  have h := X7E12_bar_mem V
  exact ⟨(Matrix.mem_unitaryGroup_iff').mp h, (Matrix.mem_unitaryGroup_iff).mp h⟩

lemma X7E12_kk_unit {d : ℕ} (V : G d) : (Matrix.kronecker V.val V.val)ᴴ * Matrix.kronecker V.val V.val = 1 ∧
    Matrix.kronecker V.val V.val * (Matrix.kronecker V.val V.val)ᴴ = 1 := by
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    X7E12_unit_left, X7E12_unit_right, Matrix.one_kronecker_one]
  simp

lemma X7E12_adm_pt {d : ℕ} (V W : G d) (X : Matrix (CombReg d) (CombReg d) ℂ)
    (R0 : Matrix (PairReg d × Fin d) (PairReg d × Fin d) ℂ)
    (hX : X.PosSemidef) (hR0 : R0.PosSemidef)
    (h1 : ∀ a b i j k l, (∑ o : PairReg d, X (a,(i,(k,o))) (b,(j,(l,o)))) =
        if k = l then R0 (a,i) (b,j) else 0)
    (h2 : ∀ a b, (∑ i : Fin d, R0 (a,i) (b,i)) = if a = b then 1 else 0) :
    (K V.val W.val * X * (K V.val W.val)ᴴ).PosSemidef ∧
    (Bm V.val * R0 * (Bm V.val)ᴴ).PosSemidef ∧
    (∀ a b i j k l, (∑ o : PairReg d, (K V.val W.val * X * (K V.val W.val)ᴴ) (a,(i,(k,o))) (b,(j,(l,o)))) =
        if k = l then (Bm V.val * R0 * (Bm V.val)ᴴ) (a,i) (b,j) else 0) ∧
    (∀ a b, (∑ i : Fin d, (Bm V.val * R0 * (Bm V.val)ᴴ) (a,i) (b,i)) = if a = b then 1 else 0) := by
  refine ⟨hX.mul_mul_conjTranspose_same _, hR0.mul_mul_conjTranspose_same _, ?_, ?_⟩
  · have htr : trR (X.submatrix (e3 d) (e3 d)) = Matrix.kronecker R0 1 := by
      ext ⟨⟨a, i⟩, k⟩ ⟨⟨b, j⟩, l⟩
      simp only [trR, e3, Matrix.submatrix_apply, Equiv.coe_fn_mk, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply]
      rw [h1]
      split_ifs <;> simp
    intro a b i j k l
    have : (∑ o : PairReg d, (K V.val W.val * X * (K V.val W.val)ᴴ) (a,(i,(k,o))) (b,(j,(l,o)))) =
        trR ((K V.val W.val * X * (K V.val W.val)ᴴ).submatrix (e3 d) (e3 d)) ((a,i),k) ((b,j),l) := rfl
    rw [this, X7E12_sub_conj, X7E12_K_sub, X7E12_trR_conj _ _ (X7E12_kk_unit W).1, htr]
    simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      (X7E12_bar_unit W).2, Matrix.mul_one, Matrix.kroneckerMap_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro a b
    have htr : trR R0 = 1 := by
      ext a b
      simp only [trR]
      rw [h2, Matrix.one_apply]
    have : (∑ i : Fin d, (Bm V.val * R0 * (Bm V.val)ᴴ) (a,i) (b,i)) =
        trR (Bm V.val * R0 * (Bm V.val)ᴴ) a b := rfl
    rw [this, Bm, X7E12_trR_conj _ _ (X7E12_bar_unit V).1, htr, Matrix.mul_one,
      (X7E12_kk_unit V).2, Matrix.one_apply]

lemma X7E12_int_entry {d : ℕ} {m : Type*} [Fintype m] (F : G d → Matrix m m ℂ) (hF : Continuous F)
    (p q : m) : Integrable (fun g => F g p q) (Schur.unitaryHaar d) :=
  (hF.matrix_elem p q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma X7E12_adm_int {d : ℕ} (F : G d → Matrix (CombReg d) (CombReg d) ℂ)
    (R : G d → Matrix (PairReg d × Fin d) (PairReg d × Fin d) ℂ)
    (hF : Continuous F) (hR : Continuous R)
    (h : ∀ g, (F g).PosSemidef ∧ (R g).PosSemidef ∧
      (∀ a b i j k l, (∑ o : PairReg d, F g (a,(i,(k,o))) (b,(j,(l,o)))) =
        if k = l then R g (a,i) (b,j) else 0) ∧
      (∀ a b, (∑ i : Fin d, R g (a,i) (b,i)) = if a = b then 1 else 0)) :
    CloningAdmissible (∫ g, F g ∂(Schur.unitaryHaar d)) := by
  have hFi : Integrable F (Schur.unitaryHaar d) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRi : Integrable R (Schur.unitaryHaar d) :=
    hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨X7E12_psd_int F hF (fun g => (h g).1), ∫ g, R g ∂(Schur.unitaryHaar d),
    X7E12_psd_int R hR (fun g => (h g).2.1), ?_, ?_⟩
  · intro a b i j k l
    simp only [X7E12_entry _ hFi]
    rw [← integral_finset_sum _ (fun o _ => X7E12_int_entry F hF _ _)]
    simp only [(h _).2.2.1]
    split_ifs
    · rw [X7E12_entry _ hRi]
    · simp
  · intro a b
    simp only [X7E12_entry _ hRi]
    rw [← integral_finset_sum _ (fun o _ => X7E12_int_entry R hR _ _)]
    simp only [(h _).2.2.2]
    simp

lemma X7E12_Bm_cont {d : ℕ} : Continuous fun V : G d => Bm V.val := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  simp only [Bm, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply]
  have h : ∀ i j, Continuous fun U : G d => U.val i j := fun i j => X7E12_val_cont.matrix_elem i j
  have h' : ∀ i j, Continuous fun U : G d => conj (U.val i j) := fun i j =>
    Complex.continuous_conj.comp (h i j)
  exact ((h _ _).mul (h _ _)).mul (h' _ _)

lemma X7E12_adm_Sw {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) (hR : CloningAdmissible R) :
    CloningAdmissible (Sw R) := by
  obtain ⟨hRp, R0, hR0, h1, h2⟩ := hR
  have hBc : Continuous fun V : G d => Bm V.val * R0 * (Bm V.val)ᴴ :=
    (X7E12_Bm_cont.matrix_mul continuous_const).matrix_mul X7E12_Bm_cont.matrix_conjTranspose
  have hKc : Continuous fun V : G d => K V.val 1 * R * (K V.val 1)ᴴ := by
    have h := X7E12_K_cont (fun V : G d => V.val) (fun _ => 1) X7E12_val_cont continuous_const
    exact (h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose
  have hTV : CloningAdmissible (TV R) := X7E12_adm_int _ _ hKc hBc
    (fun V => X7E12_adm_pt V 1 R R0 hRp hR0 h1 h2)
  obtain ⟨hTp, S0, hS0, g1, g2⟩ := hTV
  have hKc' : Continuous fun W : G d => K 1 W.val * TV R * (K 1 W.val)ᴴ := by
    have h := X7E12_K_cont (fun _ => 1) (fun V : G d => V.val) continuous_const X7E12_val_cont
    exact (h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose
  have hB1 : Bm (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    simp [Bm, Matrix.kronecker, Matrix.one_kronecker_one]
  refine X7E12_adm_int (fun W : G d => K 1 W.val * TV R * (K 1 W.val)ᴴ) (fun _ => S0) hKc'
    continuous_const (fun W => ?_)
  have := X7E12_adm_pt 1 W (TV R) S0 hTp hS0 g1 g2
  simpa [hB1] using this

lemma X7E12_score_Sw {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) :
    combScore (Sw R) = combScore R := by
  unfold Sw TW TV
  rw [X7E12_score_twirl (fun W : G d => K 1 W.val), X7E12_score_twirl (fun V : G d => K V.val 1)]
  · intro g; simpa using X7E12_Om_inv g 1
  · exact X7E12_K_cont (fun V : G d => V.val) (fun _ => 1) X7E12_val_cont continuous_const
  · intro g; simpa using X7E12_Om_inv 1 g
  · exact X7E12_K_cont (fun _ => 1) (fun V : G d => V.val) continuous_const X7E12_val_cont

end X7E12

open MeasureTheory QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Claimed50.P27 X7E12 in
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (R : Matrix (CombReg d) (CombReg d) ℂ) (hR : CloningAdmissible R) :
    ∃ S : Matrix (CombReg d) (CombReg d) ℂ,
      CloningAdmissible S ∧ combScore S = combScore R ∧ CloningCovariant S :=
  ⟨Sw R, X7E12_adm_Sw R hR, X7E12_score_Sw R, X7E12_Sw_cov R⟩
