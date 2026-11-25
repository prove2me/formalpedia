-- Prove2me | solution 1 for ReciprocityTheory.PGsh.lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:31:06.695801+00:00
-- url     : https://prove2.me/submissions/4ec6185e-237a-4e2b-8dc3-20a0d28ab8cb

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Theorems.Thm_ReciprocityTheory_PGsh_ATower_char_R
import Theorems.Thm_ReciprocityTheory_PGsh_BX_exists_lift
import Theorems.Thm_ReciprocityTheory_PGsh_BX_exists_lim_tensor
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_map
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_mul_p
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_unique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_lift_down
import Theorems.Thm_ReciprocityTheory_PGsh_BX_lift_indep
import Theorems.Thm_ReciprocityTheory_PGsh_BX_tw_qr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) :
    LimStatement B Tw Dt := by
  intro ι τ hτ hc
  have hN : ∀ n, ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := fun n => Tw.toATower.char_R n
  have hy : ∀ i n, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i n => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hex : ∀ i n, ∃ h, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n)) h :=
    fun i n => BX.isHeight_exists (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n)
  choose h hh using hex
  have hcomp : ∀ i n, (Tw.r n).1.toLinearMap ∘ₗ h i (n + 1) = h i n := by
    intro i n
    have H1 := BX.isHeight_map (B := B) hB1 (Dt.Dp (n + 1)) (Dt.Dp n) (Tw.r n) (Dt.d n) (Dt.d_π n)
      (Dt.d_σ n) (Dt.d_η n) _ _ _ (hh i (n + 1))
    rw [← B.map_comp, BX.tw_qr Tw n, pow_succ] at H1
    have hy1 : (p ^ (n + 1) * p) • B.map (Tw.q n) (τ i (n + 1)) = 0 := by
      rw [← pow_succ, ← map_nsmul, hτ i (n + 1), map_zero]
    have H2 := BX.isHeight_mul_p (B := B) hB1 (Dt.Dp n) (p ^ (n + 1)) p (hN n) _ hy1 _ H1
    rw [← map_nsmul, ← hc i n] at H2
    exact BX.isHeight_unique (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n) _ _ H2 (hh i n)
  have hlimv : ∀ i (v : B.gg), ∃ a : (Tw.O : Type u), ∀ n, (Tw.q n).1 a = h i n v := fun i v =>
    Tw.complete (fun n => h i n v) (fun n => by
      have := LinearMap.congr_fun (hcomp i n) v
      simpa using this)
  choose hta hta_spec using hlimv
  have hsep : ∀ a b : (Tw.O : Type u), (∀ n, (Tw.q n).1 a = (Tw.q n).1 b) → a = b := fun a b hab =>
    sub_eq_zero.mp (Tw.sep _ (fun n => by rw [map_sub, hab n, sub_self]))
  let ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u) := fun i =>
    { toFun := hta i
      map_add' := fun v w => hsep _ _ (fun n => by simp only [map_add, hta_spec])
      map_smul' := fun c v => hsep _ _ (fun n => by simp only [map_smul, hta_spec, RingHom.id_apply]) }
  have hlift : ∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) :=
    fun i n => BX.exists_lift (B := B) Tw.toATower n _ (hy i n)
  choose th w hthw using hlift
  have hwb : ∀ i n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
      (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap (w i (n + 1))) =
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := by
    intro i n
    obtain ⟨d1, d2, d3⟩ := BX.lift_down (B := B) Tw n (τ i (n + 1)) (th i (n + 1)) (w i (n + 1))
      (hthw i (n + 1)).1 (hthw i (n + 1)).2
    rw [← d3]
    apply BX.lift_indep (B := B) Tw.toATower n _ _ _ _ ?_ d2 (hthw i n).2
    rw [d1, ← hc i n, (hthw i n).1]
  have hbt : ∀ i, ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n,
      LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt =
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := fun i =>
    BX.exists_lim_tensor (B := B) Tw (fun n => LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n))
      (hwb i)
  choose bt hbt using hbt
  refine ⟨ht, bt, fun i n => ?_, fun i n => ⟨th i n, w i n, (hthw i n).1, (hthw i n).2, (hbt i n).symm⟩⟩
  have hq : (Tw.q n).1.toLinearMap ∘ₗ ht i = h i n := by
    ext v
    simp [ht, hta_spec]
  rw [hq]
  exact hh i n
end ReciprocityTheory.PGsh
