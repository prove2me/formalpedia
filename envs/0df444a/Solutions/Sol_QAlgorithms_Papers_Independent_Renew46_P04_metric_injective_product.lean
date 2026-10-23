-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_injective_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:02:53.36181+00:00
-- url     : https://prove2.me/submissions/0d753127-1fe7-4d98-a274-d5c2a6aa7b63

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

open Filter Set

open scoped Topology TensorProduct ENNReal

namespace X7Inj

open QAlgorithms.Papers.Independent.Renew46.P04

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace


variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem X7I_pair_eta {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (m : (b : Bool) → Factors A B b) : pair (m false).down (m true).down = m := by
  funext b; cases b <;> rfl

/-- elementary tensor in the injective model -/
def ee (x : X) (y : Y) : Bilinear K (X →L[K] K) (Y →L[K] K) K :=
  injectiveEmbedding (K := K) (PiTensorProduct.tprod K (pair x y))

theorem ee_apply (x : X) (y : Y) (m : (b : Bool) → Factors (X →L[K] K) (Y →L[K] K) b) :
    ee (K := K) x y m = (m false).down x * (m true).down y := by
  have h : ee (K := K) x y (pair (m false).down (m true).down) =
      (m false).down x * (m true).down y := by
    simp [ee, injectiveEmbedding, dualBilinear, pair, NormedSpace.dual_def]
  rwa [X7I_pair_eta] at h

theorem ee_norm (x : X) (y : Y) : ‖ee (K := K) x y‖ ≤ ‖x‖ * ‖y‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [ee_apply, Fintype.prod_bool, norm_mul]
  change ‖(m false).down x‖ * ‖(m true).down y‖ ≤
    ‖x‖ * ‖y‖ * (‖(m true).down‖ * ‖(m false).down‖)
  calc ‖(m false).down x‖ * ‖(m true).down y‖
      ≤ (‖(m false).down‖ * ‖x‖) * (‖(m true).down‖ * ‖y‖) :=
        mul_le_mul ((m false).down.le_opNorm x) ((m true).down.le_opNorm y) (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

theorem ee_add_left (a b : X) (y : Y) : ee (K := K) (a + b) y = ee a y + ee b y := by
  ext m; simp only [ContinuousMultilinearMap.add_apply, ee_apply, map_add]; ring
theorem ee_add_right (x : X) (a b : Y) : ee (K := K) x (a + b) = ee x a + ee x b := by
  ext m; simp only [ContinuousMultilinearMap.add_apply, ee_apply, map_add]; ring
theorem ee_sub_left (a b : X) (y : Y) : ee (K := K) (a - b) y = ee a y - ee b y := by
  ext m; simp only [ContinuousMultilinearMap.sub_apply, ee_apply, map_sub]; ring
theorem ee_sub_right (x : X) (a b : Y) : ee (K := K) x (a - b) = ee x a - ee x b := by
  ext m; simp only [ContinuousMultilinearMap.sub_apply, ee_apply, map_sub]; ring
theorem ee_smul_left (c : K) (a : X) (y : Y) : ee (K := K) (c • a) y = c • ee a y := by
  ext m; simp only [ContinuousMultilinearMap.smul_apply, ee_apply, map_smul, smul_eq_mul]; ring
theorem ee_smul_right (c : K) (x : X) (a : Y) : ee (K := K) x (c • a) = c • ee x a := by
  ext m; simp only [ContinuousMultilinearMap.smul_apply, ee_apply, map_smul, smul_eq_mul]; ring

theorem ee_rep (u : Algebraic K X Y) : ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
    injectiveEmbedding (K := K) u = ∑ i, ee (x i) (y i) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod c m =>
    refine ⟨1, fun _ => c • (m false).down, fun _ => (m true).down, ?_⟩
    rw [Fin.sum_univ_one, map_smul, ee_smul_left]
    conv_lhs => rw [← X7I_pair_eta m]
    rfl
  | add a b ha hb =>
    obtain ⟨n, x, y, hn⟩ := ha
    obtain ⟨k, x', y', hk⟩ := hb
    refine ⟨n + k, Fin.append x x', Fin.append y y', ?_⟩
    rw [map_add, hn, hk, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

/-- adjoint action on the first factor -/
def adjF (P : X →L[K] X) :
    Factors (X →L[K] K) (Y →L[K] K) false →L[K] Factors (X →L[K] K) (Y →L[K] K) false :=
  LinearMap.mkContinuous
    { toFun := fun f => (ULift.up ((ULift.down f).comp P) : ULift (X →L[K] K))
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
    ‖P‖ (fun f => by
      change ‖(ULift.down f).comp P‖ ≤ ‖P‖ * ‖ULift.down f‖
      rw [mul_comm]; exact ContinuousLinearMap.opNorm_comp_le _ _)

/-- adjoint action on the second factor -/
def adjT (Q : Y →L[K] Y) :
    Factors (X →L[K] K) (Y →L[K] K) true →L[K] Factors (X →L[K] K) (Y →L[K] K) true :=
  LinearMap.mkContinuous
    { toFun := fun f => (ULift.up ((ULift.down f).comp Q) : ULift (Y →L[K] K))
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
    ‖Q‖ (fun f => by
      change ‖(ULift.down f).comp Q‖ ≤ ‖Q‖ * ‖ULift.down f‖
      rw [mul_comm]; exact ContinuousLinearMap.opNorm_comp_le _ _)

def fam (P : X →L[K] X) (Q : Y →L[K] Y) :
    (b : Bool) → Factors (X →L[K] K) (Y →L[K] K) b →L[K] Factors (X →L[K] K) (Y →L[K] K) b
  | false => adjF P
  | true => adjT Q

def Phi (P : X →L[K] X) (Q : Y →L[K] Y) :
    Bilinear K (X →L[K] K) (Y →L[K] K) K →L[K] Bilinear K (X →L[K] K) (Y →L[K] K) K :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fam P Q)

theorem Phi_apply (P : X →L[K] X) (Q : Y →L[K] Y) (B : Bilinear K (X →L[K] K) (Y →L[K] K) K)
    (m : (b : Bool) → Factors (X →L[K] K) (Y →L[K] K) b) :
    Phi P Q B m = B (pair ((m false).down.comp P) ((m true).down.comp Q)) := by
  simp only [Phi, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext b; cases b <;> rfl

theorem Phi_ee (P : X →L[K] X) (Q : Y →L[K] Y) (x : X) (y : Y) :
    Phi P Q (ee (K := K) x y) = ee (P x) (Q y) := by
  ext m
  rw [Phi_apply, ee_apply, ee_apply]
  rfl

theorem Phi_norm (P : X →L[K] X) (Q : Y →L[K] Y) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖Phi P Q‖ ≤ 1 := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le _ _).trans ?_
  rw [Fintype.prod_bool]
  have h1 : ‖fam P Q true‖ ≤ 1 := by
    show ‖adjT (K := K) (X := X) Q‖ ≤ 1
    unfold adjT
    exact (LinearMap.mkContinuous_norm_le _ (norm_nonneg Q) _).trans hQ
  have h2 : ‖fam P Q false‖ ≤ 1 := by
    show ‖adjF (K := K) (Y := Y) P‖ ≤ 1
    unfold adjF
    exact (LinearMap.mkContinuous_norm_le _ (norm_nonneg P) _).trans hP
  calc ‖fam P Q true‖ * ‖fam P Q false‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem Phi_le (P : X →L[K] X) (Q : Y →L[K] Y) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (B : Bilinear K (X →L[K] K) (Y →L[K] K) K) : ‖Phi P Q B‖ ≤ ‖B‖ :=
  ((Phi P Q).le_opNorm B).trans (mul_le_of_le_one_left (norm_nonneg B) (Phi_norm P Q hP hQ))

theorem Phi_idem (P : X →L[K] X) (Q : Y →L[K] Y) (hP : P.comp P = P) (hQ : Q.comp Q = Q) :
    (Phi (K := K) P Q).comp (Phi P Q) = Phi P Q := by
  ext B m
  rw [ContinuousLinearMap.comp_apply, Phi_apply, Phi_apply]
  have e : pair (((pair ((m false).down.comp P) ((m true).down.comp Q) :
      (b : Bool) → Factors (X →L[K] K) (Y →L[K] K) b) false).down.comp P)
      (((pair ((m false).down.comp P) ((m true).down.comp Q) :
      (b : Bool) → Factors (X →L[K] K) (Y →L[K] K) b) true).down.comp Q) =
      (pair ((m false).down.comp P) ((m true).down.comp Q) :
        (b : Bool) → Factors (X →L[K] K) (Y →L[K] K) b) := by
    change pair (((m false).down.comp P).comp P) (((m true).down.comp Q).comp Q) = _
    rw [ContinuousLinearMap.comp_assoc, hP, ContinuousLinearMap.comp_assoc, hQ]
  rw [e, Phi_apply]

theorem Phi_sum (P : X →L[K] X) (Q : Y →L[K] Y) {n : ℕ} (x : Fin n → X) (y : Fin n → Y) :
    Phi P Q (∑ i, ee (K := K) (x i) (y i)) = ∑ i, ee (P (x i)) (Q (y i)) := by
  rw [map_sum]; simp only [Phi_ee]

theorem sum_ee_mem {n : ℕ} (x : Fin n → X) (y : Fin n → Y) :
    ∑ i, ee (K := K) (x i) (y i) ∈ LinearMap.range (injectiveEmbedding (K := K) (X := X) (Y := Y)) :=
  Submodule.sum_mem _ fun i _ => ⟨_, rfl⟩

theorem Phi_maps (P : X →L[K] X) (Q : Y →L[K] Y) :
    InjectiveProduct (K := K) (X := X) (Y := Y) ≤
      (InjectiveProduct (K := K) (X := X) (Y := Y)).comap (Phi P Q : _ →ₗ[K] _) := by
  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rintro _ ⟨u, rfl⟩
    obtain ⟨n, x, y, hu⟩ := ee_rep (K := K) u
    show Phi P Q (injectiveEmbedding u) ∈ InjectiveProduct (K := K) (X := X) (Y := Y)
    rw [hu, Phi_sum]
    exact Submodule.le_topologicalClosure _ (sum_ee_mem _ _)
  · exact (Submodule.isClosed_topologicalClosure
      (LinearMap.range (injectiveEmbedding (K := K) (X := X) (Y := Y)))).preimage
      (Phi P Q).continuous

theorem Phi_fd (P : X →L[K] X) (Q : Y →L[K] Y) (hA : FiniteDimensional K P.range)
    (hB : FiniteDimensional K Q.range) :
    ∃ V : Submodule K (Bilinear K (X →L[K] K) (Y →L[K] K) K), FiniteDimensional K V ∧
      InjectiveProduct (K := K) (X := X) (Y := Y) ≤ V.comap (Phi P Q : _ →ₗ[K] _) := by
  let β : LinearMap.range (P : X →ₗ[K] X) →ₗ[K] LinearMap.range (Q : Y →ₗ[K] Y) →ₗ[K]
      Bilinear K (X →L[K] K) (Y →L[K] K) K :=
    LinearMap.mk₂ K (fun a b => ee (K := K) (a : X) (b : Y))
      (fun a a' b => by simp only [Submodule.coe_add, ee_add_left])
      (fun c a b => by simp only [Submodule.coe_smul, ee_smul_left])
      (fun a b b' => by simp only [Submodule.coe_add, ee_add_right])
      (fun c a b => by simp only [Submodule.coe_smul, ee_smul_right])
  let V := LinearMap.range (TensorProduct.lift β)
  haveI : FiniteDimensional K (LinearMap.range (P : X →ₗ[K] X)) := hA
  haveI : FiniteDimensional K (LinearMap.range (Q : Y →ₗ[K] Y)) := hB
  haveI : FiniteDimensional K V := LinearMap.finiteDimensional_range _
  refine ⟨V, this, ?_⟩
  have hpure : ∀ x y, ee (K := K) (P x) (Q y) ∈ V := by
    intro x y
    exact ⟨(⟨P x, LinearMap.mem_range_self _ x⟩ : LinearMap.range (P : X →ₗ[K] X)) ⊗ₜ
      (⟨Q y, LinearMap.mem_range_self _ y⟩ : LinearMap.range (Q : Y →ₗ[K] Y)), by
        rw [TensorProduct.lift.tmul]; rfl⟩
  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rintro _ ⟨u, rfl⟩
    obtain ⟨n, x, y, hu⟩ := ee_rep (K := K) u
    show Phi P Q (injectiveEmbedding u) ∈ V
    rw [hu, Phi_sum]
    exact Submodule.sum_mem _ fun i _ => hpure _ _
  · exact (Submodule.closed_of_finiteDimensional V).preimage (Phi P Q).continuous

theorem X7I_lemA {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] (h : MetricPi K E)
    (t : Finset E) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : E →L[K] E, P.comp P = P ∧ ‖P‖ ≤ 1 ∧ FiniteDimensional K P.range ∧
      ∀ x ∈ t, ‖x - P x‖ ≤ 2 * δ * ‖x‖ := by
  classical
  let t' := (t.filter (· ≠ 0)).image (fun x => ((‖x‖ : K))⁻¹ • x)
  have hunit : ∀ x : E, x ≠ 0 → ‖((‖x‖ : K))⁻¹ • x‖ = 1 := by
    intro x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hx0, inv_mul_cancel₀ hx0.ne']
  obtain ⟨P, h1, h2, h3, h4⟩ := h δ hδ t' (by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    exact hunit x' (Finset.mem_filter.1 hx').2)
  refine ⟨P, h1, h2, h3, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set u := ((‖x‖ : K))⁻¹ • x with hu
  have hut : u ∈ t' := Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx, hx0⟩, rfl⟩
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := h4 u hut
  have hPy : P (P w) = P w := by
    have := congrArg (fun T : E →L[K] E => T w) h1
    simpa using this
  have hy' : ‖u - P w‖ < δ := hy
  have hb : ‖u - P u‖ ≤ 2 * δ := by
    have e : u - P u = (u - P w) - P (u - P w) := by rw [map_sub, hPy]; abel
    rw [e]
    calc ‖(u - P w) - P (u - P w)‖ ≤ ‖u - P w‖ + ‖P (u - P w)‖ := norm_sub_le _ _
      _ ≤ ‖u - P w‖ + ‖u - P w‖ := by
          gcongr
          exact (P.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) h2)
      _ ≤ 2 * δ := by linarith
  have hxu : x = ((‖x‖ : K)) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxp.ne'), one_smul]
  rw [hxu, map_smul, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_of_pos hxp]
  rw [← hxu]
  nlinarith

set_option maxHeartbeats 1000000 in
theorem X7I_main (hX : MetricPi K X) (hY : MetricPi K Y) :
    MetricPi K (InjectiveProduct (K := K) (X := X) (Y := Y)) := by
  classical
  intro ε hε s hs
  have hrep : ∀ z : InjectiveProduct (K := K) (X := X) (Y := Y),
      ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
        ‖(z : Bilinear K (X →L[K] K) (Y →L[K] K) K) - ∑ i, ee (K := K) (x i) (y i)‖ < ε / 3 := by
    intro z
    have hz : (z : Bilinear K (X →L[K] K) (Y →L[K] K) K) ∈
        closure (LinearMap.range (injectiveEmbedding (K := K) (X := X) (Y := Y)) :
          Set (Bilinear K (X →L[K] K) (Y →L[K] K) K)) := z.2
    obtain ⟨w, ⟨u, rfl⟩, hw⟩ := Metric.mem_closure_iff.1 hz (ε / 3) (by linarith)
    obtain ⟨n, x, y, hu⟩ := ee_rep (K := K) u
    refine ⟨n, x, y, ?_⟩
    rw [← dist_eq_norm, ← hu]; exact hw
  choose n xs ys hxy using hrep
  set M : ℝ := ∑ z ∈ s, ∑ i, ‖xs z i‖ * ‖ys z i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  set δ : ℝ := ε / (6 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨A, hA1, hA2, hA3, hA4⟩ :=
    X7I_lemA (K := K) hX (s.biUnion fun z => Finset.univ.image (xs z)) δ hδ0
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ :=
    X7I_lemA (K := K) hY (s.biUnion fun z => Finset.univ.image (ys z)) δ hδ0
  have hmaps := Phi_maps (K := K) A B
  let R : InjectiveProduct (K := K) (X := X) (Y := Y) →L[K]
      InjectiveProduct (K := K) (X := X) (Y := Y) := (Phi A B).restrict (fun z hz => hmaps hz)
  have hR : ∀ z, (R z : Bilinear K (X →L[K] K) (Y →L[K] K) K) = Phi A B z := fun z => rfl
  refine ⟨R, ?_, ?_, ?_, fun z hz => ⟨R ⟨∑ i, ee (K := K) (xs z i) (ys z i),
    Submodule.le_topologicalClosure _ (sum_ee_mem _ _)⟩, ⟨_, rfl⟩, ?_⟩⟩
  · ext1 z; apply Subtype.ext
    show Phi A B (Phi A B z) = Phi A B z
    exact congrArg (fun T => T (z : Bilinear K (X →L[K] K) (Y →L[K] K) K)) (Phi_idem A B hA1 hB1)
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [one_mul]
    exact Phi_le A B hA2 hB2 z
  · obtain ⟨V, hV, hle⟩ := Phi_fd (K := K) A B hA3 hB3
    let g : R.range →ₗ[K] Bilinear K (X →L[K] K) (Y →L[K] K) K :=
      (InjectiveProduct (K := K) (X := X) (Y := Y)).subtype.comp (R.range).subtype
    have hg : Function.Injective g := fun a b hab => Subtype.ext (Subtype.ext hab)
    have hrg : LinearMap.range g ≤ V := by
      rintro _ ⟨⟨_, ⟨z, rfl⟩⟩, rfl⟩
      exact hle z.2
    haveI : FiniteDimensional K (LinearMap.range g) := Submodule.finiteDimensional_of_le hrg
    exact LinearEquiv.finiteDimensional (LinearEquiv.ofInjective g hg).symm
  · change ‖(z : Bilinear K (X →L[K] K) (Y →L[K] K) K) -
      Phi A B (∑ i, ee (K := K) (xs z i) (ys z i))‖ < ε
    rw [Phi_sum]
    have hxA : ∀ i, ‖xs z i - A (xs z i)‖ ≤ 2 * δ * ‖xs z i‖ := fun i =>
      hA4 _ (Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    have hyB : ∀ i, ‖ys z i - B (ys z i)‖ ≤ 2 * δ * ‖ys z i‖ := fun i =>
      hB4 _ (Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    have hAx : ∀ i, ‖A (xs z i)‖ ≤ ‖xs z i‖ := fun i =>
      (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA2)
    have hterm : ∀ i, ‖ee (K := K) (xs z i) (ys z i) - ee (A (xs z i)) (B (ys z i))‖ ≤
        4 * δ * (‖xs z i‖ * ‖ys z i‖) := by
      intro i
      have e : ee (K := K) (xs z i) (ys z i) - ee (A (xs z i)) (B (ys z i)) =
          ee (xs z i - A (xs z i)) (ys z i) + ee (A (xs z i)) (ys z i - B (ys z i)) := by
        rw [ee_sub_left, ee_sub_right]; abel
      rw [e]
      calc _ ≤ ‖ee (K := K) (xs z i - A (xs z i)) (ys z i)‖ +
            ‖ee (K := K) (A (xs z i)) (ys z i - B (ys z i))‖ := norm_add_le _ _
        _ ≤ ‖xs z i - A (xs z i)‖ * ‖ys z i‖ + ‖A (xs z i)‖ * ‖ys z i - B (ys z i)‖ :=
            add_le_add (ee_norm _ _) (ee_norm _ _)
        _ ≤ (2 * δ * ‖xs z i‖) * ‖ys z i‖ + ‖xs z i‖ * (2 * δ * ‖ys z i‖) := by
            gcongr
            · exact hxA i
            · exact hAx i
            · exact hyB i
        _ = 4 * δ * (‖xs z i‖ * ‖ys z i‖) := by ring
    have hzM : ∑ i, ‖xs z i‖ * ‖ys z i‖ ≤ M :=
      Finset.single_le_sum (f := fun z => ∑ i, ‖xs z i‖ * ‖ys z i‖)
        (fun z _ => Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hz
    have hw : ‖∑ i, ee (K := K) (xs z i) (ys z i) - ∑ i, ee (A (xs z i)) (B (ys z i))‖
        ≤ 4 * δ * M := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hzM (by positivity)
    have h4 : 4 * δ * M < 2 * ε / 3 := by
      rw [hδ]
      rw [show 4 * (ε / (6 * (M + 1))) * M = (2 * ε / 3) * (M / (M + 1)) by field_simp; ring]
      have : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
      have h2 : 0 < 2 * ε / 3 := by positivity
      nlinarith
    calc ‖(z : Bilinear K (X →L[K] K) (Y →L[K] K) K) - ∑ i, ee (A (xs z i)) (B (ys z i))‖
        ≤ ‖(z : Bilinear K (X →L[K] K) (Y →L[K] K) K) - ∑ i, ee (K := K) (xs z i) (ys z i)‖ +
          ‖∑ i, ee (K := K) (xs z i) (ys z i) - ∑ i, ee (A (xs z i)) (B (ys z i))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 3 + 2 * ε / 3 := add_lt_add_of_lt_of_le (hxy z) (hw.trans h4.le)
      _ = ε := by ring

end X7Inj

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section InjectiveProduct

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

open QAlgorithms.Papers.Independent.Renew46.P04 in
theorem solution [CompleteSpace X] [CompleteSpace Y] (hX : MetricPi K X) (hY : MetricPi K Y) :
    MetricPi K (InjectiveProduct (K := K) (X := X) (Y := Y)) :=
  X7Inj.X7I_main hX hY

end InjectiveProduct
