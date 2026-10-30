-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_of_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:57:47.52599+00:00
-- url     : https://prove2.me/submissions/3d2f9a88-5cac-48bb-9859-f079a6b89625

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (m : Nat)
    (length : Fin m → Nat)
    (corner : ∀ f, Fin (length f) → V)
    (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart)
    (htail : ∀ f i, (dart ⟨f, i⟩).fst = corner f i)
    (hhead : ∀ f i, (dart ⟨f, i⟩).snd = corner f ⟨(i.val + 1) % length f, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)
    (hdistinct : ∀ f, Function.Injective (corner f))
    (hcovered : ∀ v, ∃ f i, corner f i = v)
    (hconnected : H.Connected)
    (hlen : ∀ f, 3 ≤ length f)
    (hrotation : ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart =>
          dart ⟨(dart.symm a.symm).1,
            ⟨(((dart.symm a.symm).2).val + 1) % length ((dart.symm a.symm).1),
              Nat.mod_lt _ (Nat.zero_lt_of_lt ((dart.symm a.symm).2).isLt)⟩⟩)^[k] d = e)
    (heuler : m + Fintype.card V = H.edgeSet.ncard + 2)
    (hcorners : (∑ f : Fin m, length f) = 2 * H.edgeSet.ncard)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∃ n : Nat, Nonempty (WilliamsonShmoys.TriangularMap H (Fin n)) := by
  -- every face has length exactly 3
  have hsum : (∑ f : Fin m, length f) = ∑ _f : Fin m, 3 := by
    have h1 : (∑ _f : Fin m, 3) ≤ ∑ f : Fin m, length f := Finset.sum_le_sum (fun f _ => hlen f)
    have h2 : (∑ _f : Fin m, (3:ℕ)) = 3 * m := by simp [mul_comm]
    omega
  have hl : ∀ f, length f = 3 := by
    intro f
    have := (Finset.sum_eq_sum_iff_of_le (fun f _ => hlen f)).1 hsum.symm f (Finset.mem_univ _)
    omega
  let e : (Fin m × Fin 3) ≃ (Σ f : Fin m, Fin (length f)) :=
    (Equiv.sigmaEquivProd (Fin m) (Fin 3)).symm.trans
      (Equiv.sigmaCongrRight (fun f => finCongr (hl f).symm))
  have he : ∀ f i, e (f, i) = ⟨f, Fin.cast (hl f).symm i⟩ := fun f i => rfl
  have hsig : ∀ f (x y : Fin (length f)), x.val = y.val →
      (⟨f, x⟩ : Σ f : Fin m, Fin (length f)) = ⟨f, y⟩ := by
    intro f x y h; rw [Fin.ext h]
  refine ⟨m, ⟨{
    corner := fun f i => corner f (Fin.cast (hl f).symm i)
    dart := e.trans dart
    dart_tail := fun f i => by simp only [Equiv.trans_apply, he]; exact htail _ _
    dart_head := fun f i => by
      simp only [Equiv.trans_apply, he]
      rw [hhead]; congr 1; ext; simp only [Fin.val_cast, Fin.val_add]
      rw [hl f]; simp
    corners_distinct := fun f => (hdistinct f).comp (Fin.cast_injective _)
    vertex_covered := fun v => by
      obtain ⟨f, i, h⟩ := hcovered v
      exact ⟨f, Fin.cast (hl f) i, by simpa using h⟩
    connected := hconnected
    rotation_transitive := ?_ }⟩⟩
  intro d d' hd
  obtain ⟨k, hk⟩ := hrotation d d' hd
  refine ⟨k, ?_⟩
  convert hk using 2
  funext a
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply]
  congr 1
  generalize hs : dart.symm a.symm = s
  obtain ⟨f, j⟩ := s
  have : e.symm ⟨f, j⟩ = (f, Fin.cast (hl f) j) := by
    apply e.injective; rw [Equiv.apply_symm_apply, he]; apply hsig; simp
  rw [this, he]
  apply hsig
  simp only [Fin.val_cast, Fin.val_add]
  obtain ⟨jv, hjv⟩ := j
  have h3 := hl f
  simp only [h3]
  rfl
