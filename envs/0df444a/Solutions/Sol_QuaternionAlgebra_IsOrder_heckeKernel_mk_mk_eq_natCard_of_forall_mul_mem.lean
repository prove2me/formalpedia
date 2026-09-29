-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2518d934-bbef-5213-b6e8-1b87c29bfea3

import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra

namespace DEP0

variable {a b : ℚ}

local notation "𝔸H" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ)
    {c : FiniteAdeleRing (𝓞 ℚ) ℚ} (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem finiteAdeleBox_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (h : S ≤ R) :
    Submodule.finiteAdeleBox S ≤ Submodule.finiteAdeleBox R := by
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem one_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_finiteAdeleBox hΛ.one_mem fun v => one_mem _

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    induction hy using AddSubgroup.closure_induction with
    | mem y hy' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hy'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_finiteAdeleBox (hΛ.mul_mem hz hz') fun v => mul_mem (hc v) (hc' v)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ ihy ihy' => rw [mul_add]; exact add_mem ihy ihy'
    | neg y _ ihy => convert neg_mem ihy using 1; exact mul_neg (α := ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) _ _
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ ihx ihx' => rw [add_mul]; exact add_mem ihx ihx'
  | neg x _ ihx => convert neg_mem ihx using 1; exact neg_mul (α := ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) _ _

private theorem _root_.DEP0.mem_finiteIdeleStabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
        ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  have key : ∀ w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, w ∈ Submodule.finiteIdeleStabilizer Λ → (w : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
    intro w hw
    have h1 : (w : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) • (1 : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ (w • (Submodule.finiteAdeleBox Λ : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
      Set.smul_mem_smul_set (one_mem_finiteAdeleBox hΛ)
    rw [MulAction.mem_stabilizer_iff.mp hw, smul_eq_mul, mul_one] at h1
    exact h1
  constructor
  · intro hu
    exact ⟨key u hu, key u⁻¹ (inv_mem hu)⟩
  · rintro ⟨hu, hu'⟩
    rw [Submodule.finiteIdeleStabilizer, MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mul_mem_finiteAdeleBox hΛ hu hx
    · intro x hx
      exact ⟨(u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) • x, mul_mem_finiteAdeleBox hΛ hu' hx, smul_inv_smul u x⟩

p2m_export "DEP0" "mem_finiteIdeleStabilizer_iff"

theorem mul_mem_finiteAdeleBox_of_mul_mem {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : ∀ x y : ℍ[ℚ, a, b], x ∈ X → y ∈ X → x * y ∈ X)
    {w w' : 𝔸H} (hw : w ∈ Submodule.finiteAdeleBox X) (hw' : w' ∈ Submodule.finiteAdeleBox X) :
    w * w' ∈ Submodule.finiteAdeleBox X := by

  have step : ∀ {z : ℍ[ℚ, a, b]} (_ : z ∈ X) {s : FiniteAdeleRing (𝓞 ℚ) ℚ} (_ : ∀ v : HeightOneSpectrum (𝓞 ℚ), s v ∈ v.adicCompletionIntegers ℚ)
      {w : 𝔸H} (_ : w ∈ Submodule.finiteAdeleBox X), w * (z ⊗ₜ[ℚ] s) ∈ Submodule.finiteAdeleBox X := by
    intro z hz s hs w hw
    refine (AddSubgroup.closure_le ((Submodule.finiteAdeleBox X).comap (AddMonoidHom.mulRight (z ⊗ₜ[ℚ] s)))).2 ?_ hw
    rintro _ ⟨z', hz', s', hs', rfl⟩
    show z' ⊗ₜ[ℚ] s' * (z ⊗ₜ[ℚ] s) ∈ Submodule.finiteAdeleBox X
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z' * z, hX _ _ hz' hz, s' * s, fun v => mul_mem (hs' v) (hs v), rfl⟩
  refine (AddSubgroup.closure_le ((Submodule.finiteAdeleBox X).comap (AddMonoidHom.mulLeft w))).2 ?_ hw'
  rintro _ ⟨z, hz, s, hs, rfl⟩
  exact step hz hs hw

theorem primeHeckeSet_mul_mem_left {S : Submodule ℤ ℍ[ℚ, a, b]} (hSm : ∀ x y : ℍ[ℚ, a, b], x ∈ S → y ∈ S → x * y ∈ S) (ℓ : ℕ)
    {u : (𝔸H)ˣ} (hu : (u : 𝔸H) ∈ Submodule.finiteAdeleBox S) (hu' : ((u⁻¹ : (𝔸H)ˣ) : 𝔸H) ∈ Submodule.finiteAdeleBox S)
    {h : (𝔸H)ˣ} (hh : h ∈ primeHeckeSet S ℓ) : u * h ∈ primeHeckeSet S ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact mul_mem_finiteAdeleBox_of_mul_mem hSm hu h1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]
    exact mul_mem_finiteAdeleBox_of_mul_mem hSm h2 hu'
  · intro h5
    apply h3
    rw [mul_inv_rev, Units.val_mul] at h5
    have := mul_mem_finiteAdeleBox_of_mul_mem hSm h5 hu
    simpa [mul_assoc] using this
  · intro h5
    apply h4
    rw [Units.val_mul, ← mul_smul_comm] at h5
    have := mul_mem_finiteAdeleBox_of_mul_mem hSm hu' h5
    simpa [mul_assoc] using this

theorem primeHeckeSet_left_stable {S : Submodule ℤ ℍ[ℚ, a, b]} (hS : IsOrder S) {U : Subgroup (𝔸H)ˣ}
    (hU : U ≤ Submodule.finiteIdeleStabilizer S) (ℓ : ℕ) :
    ∀ u ∈ U, ∀ h ∈ primeHeckeSet S ℓ, u * h ∈ primeHeckeSet S ℓ := fun u hu _ hh =>
  primeHeckeSet_mul_mem_left (fun _ _ hx hy => hS.mul_mem hx hy) ℓ ((mem_finiteIdeleStabilizer_iff hS u).1 (hU hu)).1
    ((mem_finiteIdeleStabilizer_iff hS u).1 (hU hu)).2 hh

theorem mem_ofFiniteIdele_iff' (R : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔸H)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele R g ↔ ((g⁻¹ : (𝔸H)ˣ) : 𝔸H) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox R := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨t, ht, h⟩
    have h' : (g : 𝔸H) * t = z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := h
    rw [← h', Units.inv_mul_cancel_left]
    exact ht
  · intro h
    exact ⟨_, h, by simp⟩

theorem ofFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer (R : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔸H)ˣ) {u : (𝔸H)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    Submodule.ofFiniteIdele R (g * u) = Submodule.ofFiniteIdele R g := by
  ext z
  rw [mem_ofFiniteIdele_iff', mem_ofFiniteIdele_iff', mul_inv_rev, Units.val_mul, mul_assoc]

  have hst : (u⁻¹ : (𝔸H)ˣ) • ((Submodule.finiteAdeleBox R : AddSubgroup (𝔸H)) : Set (𝔸H)) =
      ((Submodule.finiteAdeleBox R : AddSubgroup (𝔸H)) : Set (𝔸H)) :=
    (Submodule.mem_finiteIdeleStabilizer_iff R u⁻¹).1 (inv_mem hu)
  constructor
  · intro h
    have h' : ((u⁻¹ : (𝔸H)ˣ) : 𝔸H) * (((g⁻¹ : (𝔸H)ˣ) : 𝔸H) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) ∈
        (u⁻¹ : (𝔸H)ˣ) • ((Submodule.finiteAdeleBox R : AddSubgroup (𝔸H)) : Set (𝔸H)) := by
      rw [hst]; exact h
    exact Set.smul_mem_smul_set_iff.1 h'
  · intro h
    have h' : ((u⁻¹ : (𝔸H)ˣ) : 𝔸H) * (((g⁻¹ : (𝔸H)ˣ) : 𝔸H) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) ∈
        (u⁻¹ : (𝔸H)ˣ) • ((Submodule.finiteAdeleBox R : AddSubgroup (𝔸H)) : Set (𝔸H)) :=
      Set.smul_mem_smul_set h
    rwa [hst] at h'

theorem classSetMk_eq_iff_exists_ofFiniteIdele_eq_smul (R : Submodule ℤ ℍ[ℚ, a, b]) (hfg : R.FG)
    (hspan : Submodule.span ℚ (R : Set ℍ[ℚ, a, b]) = ⊤) (x y : (𝔸H)ˣ) :
    ClassSet.mk (Submodule.finiteIdeleStabilizer R) x = ClassSet.mk (Submodule.finiteIdeleStabilizer R) y ↔
      ∃ d : (ℍ[ℚ, a, b])ˣ, Submodule.ofFiniteIdele R x = d • Submodule.ofFiniteIdele R y := by
  constructor
  · intro h
    obtain ⟨δ, hδ, u, hu, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 h
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hδ
    refine ⟨d⁻¹, ?_⟩
    have h1 : Submodule.ofFiniteIdele R (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x * u) =
        Submodule.ofFiniteIdele R (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x) :=
      ((Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff R hfg hspan _ _).2 (by
        rw [show (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x * u)⁻¹ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x) = u⁻¹ by group]
        exact inv_mem hu))
    rw [h1, Submodule.ofFiniteIdele_diagonal_mul, inv_smul_smul]
  · rintro ⟨d, hd⟩
    rw [← Submodule.ofFiniteIdele_diagonal_mul, Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff R hfg hspan] at hd

    refine ((DoubleCoset.eq _ _ _ _).2 ⟨Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d⁻¹, MonoidHom.mem_range.mpr ⟨d⁻¹, rfl⟩,
      x⁻¹ * (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * y), hd, ?_⟩)
    rw [map_inv]
    group

section E7a

variable {R : Submodule ℤ ℍ[ℚ, a, b]}

noncomputable def cosetIdeal (R : Submodule ℤ ℍ[ℚ, a, b]) (x : (𝔸H)ˣ) :
    (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R → Submodule ℤ ℍ[ℚ, a, b] :=
  Quotient.lift (fun h : (𝔸H)ˣ => Submodule.ofFiniteIdele R (x * h)) fun h h' hh' => by
    have hu : h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer R := QuotientGroup.leftRel_apply.1 hh'
    show Submodule.ofFiniteIdele R (x * h) = Submodule.ofFiniteIdele R (x * h')
    rw [show x * h' = x * h * (h⁻¹ * h') by group]
    exact (ofFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer R (x * h) hu).symm

theorem cosetIdeal_mk (R : Submodule ℤ ℍ[ℚ, a, b]) (x h : (𝔸H)ˣ) :
    cosetIdeal R x (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = Submodule.ofFiniteIdele R (x * h) := rfl

theorem cosetIdeal_injective (hfg : R.FG) (hspan : Submodule.span ℚ (R : Set ℍ[ℚ, a, b]) = ⊤) (x : (𝔸H)ˣ) :
    Function.Injective (cosetIdeal R x) := by
  rintro ⟨h⟩ ⟨h'⟩ e
  change cosetIdeal R x (h : (𝔸H)ˣ ⧸ _) = cosetIdeal R x (h' : (𝔸H)ˣ ⧸ _) at e
  rw [cosetIdeal_mk, cosetIdeal_mk, Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff R hfg hspan] at e
  change (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = (h' : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R)
  exact QuotientGroup.eq.2 (by simpa [mul_assoc] using e)

noncomputable def cosetsEquivIdeals (hfg : R.FG) (hspan : Submodule.span ℚ (R : Set ℍ[ℚ, a, b]) = ⊤) (T : Set (𝔸H)ˣ) (x : (𝔸H)ˣ) :
    {c : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R // ∃ h ∈ T, (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c} ≃
      {J : Submodule ℤ ℍ[ℚ, a, b] // ∃ h ∈ T, J = Submodule.ofFiniteIdele R (x * h)} :=
  Equiv.ofBijective
    (fun c => ⟨cosetIdeal R x c.1, by
      obtain ⟨h, hh, hc⟩ := c.2
      exact ⟨h, hh, by rw [← hc, cosetIdeal_mk]⟩⟩)
    ⟨fun c c' e => Subtype.ext (cosetIdeal_injective hfg hspan x (congrArg Subtype.val e)),
     fun J => by
      obtain ⟨h, hh, hJ⟩ := J.2
      exact ⟨⟨(h : (𝔸H)ˣ ⧸ _), h, hh, rfl⟩, Subtype.ext (by rw [hJ]; rfl)⟩⟩

@[scoped simp] theorem cosetsEquivIdeals_apply_coe (hfg : R.FG) (hspan : Submodule.span ℚ (R : Set ℍ[ℚ, a, b]) = ⊤) (T : Set (𝔸H)ˣ) (x : (𝔸H)ˣ)
    (c : {c : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R // ∃ h ∈ T, (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c}) :
    ((cosetsEquivIdeals hfg hspan T x c : {J : Submodule ℤ ℍ[ℚ, a, b] // ∃ h ∈ T, J = Submodule.ofFiniteIdele R (x * h)}) :
      Submodule ℤ ℍ[ℚ, a, b]) = cosetIdeal R x c.1 := rfl

theorem heckeIncidence_iff (hfg : R.FG) (hspan : Submodule.span ℚ (R : Set ℍ[ℚ, a, b]) = ⊤) (T : Set (𝔸H)ˣ) (x y : (𝔸H)ˣ)
    (c : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) :
    (∃ h ∈ T, (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c ∧
        ClassSet.mk (Submodule.finiteIdeleStabilizer R) (x * h) = ClassSet.mk (Submodule.finiteIdeleStabilizer R) y) ↔
      (∃ h ∈ T, (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c) ∧
        ∃ d : (ℍ[ℚ, a, b])ˣ, cosetIdeal R x c = d • Submodule.ofFiniteIdele R y := by
  constructor
  · rintro ⟨h, hh, rfl, hc⟩
    exact ⟨⟨h, hh, rfl⟩, (classSetMk_eq_iff_exists_ofFiniteIdele_eq_smul R hfg hspan _ _).1 hc⟩
  · rintro ⟨⟨h, hh, rfl⟩, hd⟩
    exact ⟨h, hh, rfl, (classSetMk_eq_iff_exists_ofFiniteIdele_eq_smul R hfg hspan _ _).2 hd⟩

theorem heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem (hR : IsOrder R) (T : Set (𝔸H)ˣ)
    (hT : ∀ u ∈ Submodule.finiteIdeleStabilizer R, ∀ h ∈ T, u * h ∈ T) (x y : (𝔸H)ˣ) :
    heckeKernel (Submodule.finiteIdeleStabilizer R) T
        (ClassSet.mk (Submodule.finiteIdeleStabilizer R) x) (ClassSet.mk (Submodule.finiteIdeleStabilizer R) y) =
      Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (∃ h ∈ T, J = Submodule.ofFiniteIdele R (x * h)) ∧
          ∃ d : (ℍ[ℚ, a, b])ˣ, J = d • Submodule.ofFiniteIdele R y} := by
  rw [heckeKernel_mk _ _ hT x]

  let e₁ : HeckeIncidence (Submodule.finiteIdeleStabilizer R) T x (ClassSet.mk _ y) ≃
      {c : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R //
        (∃ h ∈ T, (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c) ∧
          ∃ d : (ℍ[ℚ, a, b])ˣ, cosetIdeal R x c = d • Submodule.ofFiniteIdele R y} :=
    Equiv.subtypeEquivRight fun c => heckeIncidence_iff hR.fg hR.spanTop T x y c
  let e₂ := (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun c : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R => ∃ h ∈ T, (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c)
      (fun c => ∃ d : (ℍ[ℚ, a, b])ˣ, cosetIdeal R x c = d • Submodule.ofFiniteIdele R y)).symm
  let e₃ : {c : {c : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R // ∃ h ∈ T, (h : (𝔸H)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c} //
        ∃ d : (ℍ[ℚ, a, b])ˣ, cosetIdeal R x c.1 = d • Submodule.ofFiniteIdele R y} ≃
      {J : {J : Submodule ℤ ℍ[ℚ, a, b] // ∃ h ∈ T, J = Submodule.ofFiniteIdele R (x * h)} //
        ∃ d : (ℍ[ℚ, a, b])ˣ, (J : Submodule ℤ ℍ[ℚ, a, b]) = d • Submodule.ofFiniteIdele R y} :=
    (cosetsEquivIdeals hR.fg hR.spanTop T x).subtypeEquiv fun c => Iff.rfl
  let e₄ := Equiv.subtypeSubtypeEquivSubtypeInter
      (fun J : Submodule ℤ ℍ[ℚ, a, b] => ∃ h ∈ T, J = Submodule.ofFiniteIdele R (x * h))
      (fun J => ∃ d : (ℍ[ℚ, a, b])ˣ, J = d • Submodule.ofFiniteIdele R y)
  exact_mod_cast Nat.card_congr (e₁.trans (e₂.trans (e₃.trans e₄)))

theorem heckeKernel_primeHeckeSet_mk_mk_eq_natCard (hR : IsOrder R) (ℓ : ℕ) (x y : (𝔸H)ˣ) :
    heckeKernel (Submodule.finiteIdeleStabilizer R) (primeHeckeSet R ℓ)
        (ClassSet.mk (Submodule.finiteIdeleStabilizer R) x) (ClassSet.mk (Submodule.finiteIdeleStabilizer R) y) =
      Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (∃ h ∈ primeHeckeSet R ℓ, J = Submodule.ofFiniteIdele R (x * h)) ∧
          ∃ d : (ℍ[ℚ, a, b])ˣ, J = d • Submodule.ofFiniteIdele R y} :=
  heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem hR (primeHeckeSet R ℓ) (primeHeckeSet_left_stable hR le_rfl ℓ) x y

end E7a

end DEP0
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem.DEP0"

theorem solution {a b : ℚ}
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hT : ∀ u ∈ Submodule.finiteIdeleStabilizer R, ∀ h ∈ T, u * h ∈ T)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    QuaternionAlgebra.heckeKernel (Submodule.finiteIdeleStabilizer R) T
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) x)
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) y) =
      Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (∃ h ∈ T, J = Submodule.ofFiniteIdele R (x * h)) ∧
          ∃ d : (ℍ[ℚ, a, b])ˣ, J = d • Submodule.ofFiniteIdele R y} :=
  DEP0.heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem hR T hT x y

end S_QuaternionAlgebra_IsOrder_heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem (solution)
