-- Prove2me | solution 1 for StickyKakeya4.maslov_incidence_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @sensei
-- created : 2026-09-26T04:14:00.509935+00:00
-- url     : https://prove2.me/submissions/b9b7b6cd-7305-4e72-aabc-84b0f6f9b014

import Definitions.Def_sticky_kakeya4_core

open StickyKakeya4

theorem solution (A B : Mat3) (s : ℝ)
    (hframe : Function.Injective (fun c : E3 => (A.mulVec c, B.mulVec c))) :
    Matrix.det (pencil A B s) = 0 ↔
      ∃ point : E3 × E3,
        point ∈ graphPlane A B ∧
        point ∈ lagrangianPencil s ∧
        point ≠ 0 := by
  constructor
  · intro hdet
    obtain ⟨v, hv, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    let c : E3 := WithLp.toLp 2 v
    let x : E3 := WithLp.toLp 2 (A.mulVec v)
    let y : E3 := WithLp.toLp 2 (B.mulVec v)
    have hc : c ≠ 0 := by
      intro hc
      apply hv
      have hvzero := congrArg (fun z : E3 => z.ofLp) hc
      simpa [c] using hvzero
    refine ⟨(x, y), ⟨c, rfl, rfl⟩, ?_, ?_⟩
    · change y = (-s) • x
      simp only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec] at hkernel
      ext i
      change B.mulVec v i = (-s) * A.mulVec v i
      have hi := congrFun hkernel i
      simp only [Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply] at hi ⊢
      linarith
    · intro hpoint
      apply hc
      apply hframe
      apply Prod.ext
      · funext i
        have hi := congrArg (fun p : E3 × E3 => p.1.ofLp i) hpoint
        simpa [x] using hi
      · funext i
        have hi := congrArg (fun p : E3 × E3 => p.2.ofLp i) hpoint
        simpa [y] using hi
  · rintro ⟨point, ⟨c, hx, hy⟩, hlagrangian, hpoint⟩
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨c.ofLp, ?_, ?_⟩
    · intro hc
      apply hpoint
      apply Prod.ext
      · have hx0 : point.1.ofLp = 0 := by
          simpa [hc] using hx
        simpa using congrArg (WithLp.toLp 2) hx0
      · have hy0 : point.2.ofLp = 0 := by
          simpa [hc] using hy
        simpa using congrArg (WithLp.toLp 2) hy0
    · change (pencil A B s).mulVec c.ofLp = 0
      change point.2 = (-s) • point.1 at hlagrangian
      have hraw : B.mulVec c.ofLp = (-s) • A.mulVec c.ofLp := by
        funext i
        have hi := congrArg (fun z : E3 => z.ofLp i) hlagrangian
        have hxi := congrFun hx i
        have hyi := congrFun hy i
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at hi
        rw [hyi, hxi] at hi
        exact hi
      simp only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec]
      funext i
      have hi := congrFun hraw i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linarith
