-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:59:22.301146+00:00
-- url     : https://prove2.me/submissions/47a3b69a-b374-4405-a338-a373bea56079

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

open QAlgorithms.Papers.Independent.Next46.P22
open scoped TensorProduct

namespace G61P

variable {F A B X : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup X] [Module F X]

theorem ts_lift (z : A ⊗[F] B) (Φ : A →ₗ[F] B →ₗ[F] X) :
    tensorSum z (fun a b => Φ a b) = TensorProduct.lift Φ z := by
  unfold tensorSum
  conv_rhs => rw [(TensorProduct.exists_finset z).choose_spec]
  simp [map_sum]

theorem ts_eq (z : A ⊗[F] B) (f : A → B → X) (Φ : A →ₗ[F] B →ₗ[F] X)
    (h : ∀ a b, f a b = Φ a b) : tensorSum z f = TensorProduct.lift Φ z := by
  have : f = fun a b => Φ a b := funext fun a => funext fun b => h a b
  subst this; exact ts_lift z Φ

theorem ts_mem (z : A ⊗[F] B) (f : A → B → X) (U : Submodule F X) (h : ∀ a b, f a b ∈ U) :
    tensorSum z f ∈ U := by
  unfold tensorSum; exact Submodule.sum_mem _ (fun p _ => h _ _)

theorem ts_bil {C D : Type*} [AddCommGroup C] [Module F C] [AddCommGroup D] [Module F D]
    (z : A ⊗[F] B) (G : A →ₗ[F] B →ₗ[F] X) (f : A → B → X) (hf : ∀ a b, f a b = G a b)
    (z' : C ⊗[F] D) (u : C → D → A) (w : C → D → B)
    (hz : z = tensorSum z' (fun x y => u x y ⊗ₜ[F] w x y)) :
    tensorSum z f = tensorSum z' (fun x y => G (u x y) (w x y)) := by
  rw [ts_eq z f G hf, hz]
  unfold tensorSum
  rw [map_sum]
  simp

theorem map_ts {Y : Type*} [AddCommGroup Y] [Module F Y] (T : X →ₗ[F] Y) (z : A ⊗[F] B) (f : A → B → X) :
    T (tensorSum z f) = tensorSum z (fun a b => T (f a b)) := by
  unfold tensorSum; rw [map_sum]

variable {H L : Type*} [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- bilinear map (x, w) ↦ ⁅α x u, α w v⁆ -/
def lam (alpha : H →ₐ[F] Module.End F L) (u v : L) : H →ₗ[F] H →ₗ[F] L :=
  LinearMap.mk₂ F (fun x w => ⁅alpha x u, alpha w v⁆)
    (by intro a b c; simp [add_lie]) (by intro c a b; simp [smul_lie])
    (by intro a b c; simp [lie_add]) (by intro c a b; simp [lie_smul])

theorem key (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) (h : H) (u v : L) :
    ⁅alpha h u, v⁆ = tensorSum (Coalgebra.comul (R := F) h)
      (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) := by
  -- Φ h1 h2 = α h1 ⁅u, α (S h2) v⁆
  let Φ : H →ₗ[F] H →ₗ[F] L := LinearMap.mk₂ F
    (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆)
    (by intro a b c; simp) (by intro c a b; simp)
    (by intro a b c; simp) (by intro c a b; simp)
  rw [ts_eq _ (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) Φ (fun _ _ => rfl)]
  -- Θ' : H ⊗ (H ⊗ H) → L
  let Θ' : H ⊗[F] (H ⊗[F] H) →ₗ[F] L :=
    TensorProduct.lift (lam alpha u v) ∘ₗ
      (LinearMap.lTensor H (LinearMap.mul' F H ∘ₗ (HopfAlgebra.antipode F (A := H)).lTensor H))
  have hΦ : TensorProduct.lift Φ = Θ' ∘ₗ (TensorProduct.assoc F H H H).toLinearMap ∘ₗ
      (Coalgebra.comul (R := F) (A := H)).rTensor H := by
    apply TensorProduct.ext'
    intro h1 h2
    simp only [TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
    show alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆ = _
    rw [ha h1 u _]
    rw [ts_eq _ (fun x y => ⁅alpha x u, alpha y (alpha (HopfAlgebra.antipode F h2) v)⁆) (lam alpha u (alpha (HopfAlgebra.antipode F h2) v)) (fun _ _ => rfl)]
    induction (Coalgebra.comul (R := F) h1) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [Θ', lam, TensorProduct.assoc_tmul, Module.End.mul_apply]
    | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add, map_add]
  rw [hΦ]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [Coalgebra.coassoc_apply]
  have hΘ : Θ' ∘ₗ (Coalgebra.comul (R := F) (A := H)).lTensor H =
      TensorProduct.lift (lam alpha u v) ∘ₗ
        LinearMap.lTensor H ((Algebra.linearMap F H) ∘ₗ Coalgebra.counit) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul]
    simp only [Θ', LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
  have := congrArg (fun f => f (Coalgebra.comul (R := F) h)) hΘ
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [this]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp [lam]

theorem ts_lam (alpha : H →ₐ[F] Module.End F L) (u v : L) (z : H ⊗[F] H) :
    tensorSum z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) = TensorProduct.lift (lam alpha u v) z :=
  ts_eq z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) (lam alpha u v) (fun _ _ => rfl)

end G61P

open QAlgorithms.Papers.Independent.Next46.P22
open Classical

section g61aL
variable {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]

/-- iterated brackets with N -/
def g61a_C (N : LieIdeal F L) : ℕ → Submodule F L
  | 0 => ⊤
  | i + 1 => Submodule.span F {w | ∃ n ∈ N, ∃ x ∈ g61a_C N i, w = ⁅n, x⁆}

theorem g61a_C_inv (N : LieIdeal F L) (i : ℕ) (l : L) (x : L) (hx : x ∈ g61a_C N i) :
    ⁅l, x⁆ ∈ g61a_C N i := by
  induction i generalizing l x with
  | zero => trivial
  | succ i ih =>
    simp only [g61a_C] at hx ⊢
    induction hx using Submodule.span_induction generalizing l with
    | mem w hw =>
      obtain ⟨n, hn, x', hx', rfl⟩ := hw
      rw [leibniz_lie]
      refine Submodule.add_mem _ (Submodule.subset_span ⟨⁅l, n⁆, N.lie_mem hn, x', hx', rfl⟩)
        (Submodule.subset_span ⟨n, hn, ⁅l, x'⁆, ih l x' hx', rfl⟩)
    | zero => simp
    | add a b _ _ ha hb => rw [lie_add]; exact Submodule.add_mem _ (ha l) (hb l)
    | smul c a _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c (ha l)

theorem g61a_C_alg (N : LieIdeal F L) (i : ℕ) (y : Module.End F L)
    (hy : y ∈ Algebra.adjoin F (Set.range (LieAlgebra.ad F L))) :
    ∀ x ∈ g61a_C N i, y x ∈ g61a_C N i := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    intro x hx; exact g61a_C_inv N i l x hx
  | algebraMap c =>
    intro x hx
    simp only [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ c hx
  | add a b _ _ ha hb => intro x hx; exact Submodule.add_mem _ (ha x hx) (hb x hx)
  | mul a b _ _ ha hb => intro x hx; exact ha _ (hb x hx)

theorem g61a_C_lcs (N : LieIdeal F L) (i : ℕ) :
    g61a_C N (i + 1) ≤ (LieModule.lowerCentralSeries F N N i).toSubmodule.map
      ({ toFun := fun x : N => (x : L), map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl } : N →ₗ[F] L) := by
  induction i with
  | zero =>
    simp only [g61a_C]
    rw [Submodule.span_le]
    rintro w ⟨n, hn, x, -, rfl⟩
    have hm : ⁅n, x⁆ ∈ N := by rw [← lie_skew]; exact N.neg_mem (N.lie_mem hn)
    exact ⟨⟨⁅n, x⁆, hm⟩, by simp, rfl⟩
  | succ i ih =>
    rw [g61a_C, Submodule.span_le]
    rintro w ⟨n, hn, x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := ih hx
    refine ⟨⁅(⟨n, hn⟩ : N), y⁆, ?_, ?_⟩
    · change ⁅(⟨n, hn⟩ : N), y⁆ ∈ LieModule.lowerCentralSeries F N N (i + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hy
    · rfl

theorem g61a_jac {A : Type*} [Ring A] (z : A) (h : ∀ y : A, IsNilpotent (y * z)) :
    z ∈ Ring.jacobson A := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  intro y
  obtain ⟨u, hu⟩ := (h y).isUnit_add_one
  refine ⟨↑u⁻¹, ?_⟩
  rw [Submodule.mem_bot]
  calc (↑u⁻¹ : A) * y * z + ↑u⁻¹ - 1 = ↑u⁻¹ * (y * z + 1) - 1 := by noncomm_ring
    _ = 0 := by rw [← hu, Units.inv_mul, sub_self]

end g61aL

theorem solution {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    (N : LieIdeal F L) (hN : LieModule.IsNilpotent N N) :
    let A := Algebra.adjoin F (Set.range (LieAlgebra.ad F L))
    ∀ a ∈ N, ∃ z : A, (z : Module.End F L) = LieAlgebra.ad F L a ∧
      z ∈ Ring.jacobson A := by
  intro A a ha
  refine ⟨⟨LieAlgebra.ad F L a, Algebra.subset_adjoin ⟨a, rfl⟩⟩, rfl, ?_⟩
  apply g61a_jac
  intro y
  obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff F N N).mp hN
  refine ⟨k + 1, ?_⟩
  have hstep : ∀ m, ∀ x : L, (((y * ⟨LieAlgebra.ad F L a, Algebra.subset_adjoin ⟨a, rfl⟩⟩ : A) ^ m :
      A) : Module.End F L) x ∈ g61a_C N m := by
    intro m
    induction m with
    | zero => intro x; trivial
    | succ m ih =>
      intro x
      rw [pow_succ', Subalgebra.coe_mul, Module.End.mul_apply, Subalgebra.coe_mul,
        Module.End.mul_apply]
      refine g61a_C_alg N (m + 1) y y.2 _ ?_
      exact Submodule.subset_span ⟨a, ha, _, ih x, rfl⟩
  apply Subtype.ext
  ext x
  have h1 := g61a_C_lcs N k (hstep (k + 1) x)
  rw [hk] at h1
  simpa using h1
