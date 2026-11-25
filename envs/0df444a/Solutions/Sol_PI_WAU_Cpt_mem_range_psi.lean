-- Prove2me | solution 1 for PI.WAU.Cpt.mem_range_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:07:06.751998+00:00
-- url     : https://prove2.me/submissions/70752ff7-4519-48c9-aa38-3ffca9b09ceb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_emb_coord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
namespace Cpt
variable (I : AutInst)
private theorem intC_smul_entry_of_preserves_Lf (d D D1 : ℕ)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hg : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F,
      v ∈ I.Lf ↔ (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf)
    (i j : Fin I.n) :
    IntC (bs I) ((D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j) := by
  classical
  have hy : ∀ j', IntC (bs I)
      ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) j') := by
    intro j'
    by_cases h : j' = j
    · rw [h, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne h]
      intro k
      simp only [map_zero, Pi.zero_apply]
      exact (Formalism.UG.intAd I.F).zero_mem
  have hL := (hg _).mp (hlow _ hy)
  have hI := hup _ hL i
  have hs : ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F)) i =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j * (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : D • ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i =
      (D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply, hs]
    simp only [nsmul_eq_mul, Nat.cast_mul, mul_one]
    ring
  rwa [key] at hI
private theorem coord_mem_Bx_of_intC_nsmul (N : ℕ) (hN : 0 < N) (z : I.E ⊗[I.F] Af I.F)
    (hz : IntC (bs I) (N • z)) (k : ιb I) : coord (bs I) z k ∈ Bx I N := by
  simp only [Bx, Set.mem_image]
  refine ⟨N • coord (bs I) z k, ?_, ?_⟩
  · have := hz k
    rwa [map_nsmul, Pi.smul_apply] at this
  · have hN' : (N : I.F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)) N, ← map_mul,
      inv_mul_cancel₀ hN', map_one, one_mul]
end Cpt
end PI.WAU
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (d D D1 : ℕ) (hN : 0 < D * (d * D1))
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    {x : I.Gf} (hx : x ∈ I.Kset) : ∃ p, psi I (D * (d * D1)) p = x := by
  classical
  have h0 : (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf := hx
  have h0i : ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹) ∈ Formalism.UG.stabGL I.Lf := inv_mem h0
  have hx' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v
        ∈ I.Lf := h0
  have hxi' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf := h0i
  have hm1 : matOf I (fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  have hm2 : matOf I (fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  refine ⟨⟨(fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j), fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)), ?_⟩, ?_⟩
  · simp only [Cset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j k
      exact ⟨coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hx' i j) k,
        coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hxi' i j) k⟩
    · rw [hm1, hm2]; exact Units.mul_inv _
    · rw [hm1, hm2]; exact Units.inv_mul _
    · rw [hm1]; exact x.2
    · intro l hl
      rw [hm1]
      exact (hx' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
    · intro l hl
      rw [hm2]
      exact (hxi' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
  · exact Subtype.ext (Units.ext hm1)
end PI.WAU.Cpt
