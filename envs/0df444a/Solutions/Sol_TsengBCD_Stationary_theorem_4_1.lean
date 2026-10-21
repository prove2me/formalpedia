-- Prove2me | solution 1 for TsengBCD.Stationary.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T12:19:04.94799+00:00
-- url     : https://prove2.me/submissions/bdbc6da4-0c2e-4484-a9e3-5a452931aaca

/-
SPDX-License-Identifier: Apache-2.0
Standalone proof of the full native Tseng block coordinate descent Theorem 4.1.
Mathematical source: P. Tseng, JOTA 109 (2001), pp. 477–483,
https://doi.org/10.1023/A:1017501703105.
The native ambient continuity at every initial-level-set point is retained.
This is not the weaker continuity-of-restriction reading of the printed theorem.
The proof constructs genuine runs, extracts actual finite state/schedule windows,
and proves all pseudoconvex and middle-block-uniqueness branches from those windows.
No accepted third-party proof implementation is copied; all proof bodies are new.
-/
import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

-- BEGIN Foundation
open Filter Topology Set

namespace TsengBCDProof
open TsengBCD.Stationary

variable {N : ℕ} {n : Fin N → ℕ}

def BlockMin (f : X n → EReal) (z : X n) (k : Fin N) : Prop :=
  ∀ a, f z ≤ f (Function.update z k a)

structure Window (f : X n → EReal) (K : Set (X n)) (T : ℕ) where
  z : Fin (T + 1) → X n
  label : Fin T → Fin N
  mem : ∀ j, z j ∈ K
  value_eq : ∀ i j, f (z i) = f (z j)
  agree : ∀ j k, k ≠ label j → z j.succ k = z j.castSucc k
  min_left : ∀ j, BlockMin f (z j.castSucc) (label j)
  min_right : ∀ j, BlockMin f (z j.succ) (label j)

end TsengBCDProof
-- END Foundation

-- BEGIN RunBasics
noncomputable section
namespace TsengBCDProof
open TsengBCD.Stationary Filter Topology Set
variable {N : ℕ} {n : Fin N → ℕ}

theorem run_descent {f : X n → EReal} {s : ℕ → Fin N} {x : ℕ → X n}
    (hr : IsBCDRun f s x) : Antitone (fun r => f (x r)) := by
  apply antitone_nat_of_succ_le
  intro r
  simpa only [Function.update_eq_self] using (hr.2 r).2 (x r (s r))

theorem run_mem {f : X n → EReal} {s : ℕ → Fin N} {x : ℕ → X n}
    (hr : IsBCDRun f s x) (x0 : X n) (h0 : x 0 = x0) :
    ∀ r, x r ∈ levelSet f x0 := by
  intro r
  change f (x r) ≤ f x0
  rw [← h0]
  exact run_descent hr (Nat.zero_le r)

theorem exists_coordinate_step (f : X n → EReal) (x0 : X n)
    (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y)
    (y : X n) (hy : y ∈ levelSet f x0) (k : Fin N) :
    ∃ z ∈ levelSet f x0, (∀ j, j ≠ k → z j = y j) ∧
      ∀ a, f z ≤ f (Function.update y k a) := by
  let S : Set (X n) := {z | z ∈ levelSet f x0 ∧ ∀ j, j ≠ k → z j = y j}
  have hsclosed : IsClosed {z : X n | ∀ j, j ≠ k → z j = y j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply j) continuous_const
  have hsc : IsCompact S := hcpt.inter_right hsclosed
  have hsn : S.Nonempty := ⟨y, hy, fun _ _ => rfl⟩
  obtain ⟨z, hz, hmin⟩ := hsc.exists_isMinOn hsn
    (fun w hw => (hcont w hw.1).continuousWithinAt)
  refine ⟨z, hz.1, hz.2, ?_⟩
  intro a
  by_cases ha : Function.update y k a ∈ levelSet f x0
  · apply hmin
    exact ⟨ha, fun j hj => Function.update_of_ne hj a y⟩
  · exact hz.1.trans (le_of_not_ge ha)

theorem exists_run (f : X n → EReal) (x0 : X n) (hx0 : f x0 ≠ ⊤)
    (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y) (s : ℕ → Fin N) :
    ∃ x : ℕ → X n, x 0 = x0 ∧ IsBCDRun f s x := by
  classical
  let K := {y : X n // y ∈ levelSet f x0}
  have hs (k : Fin N) (y : K) := exists_coordinate_step f x0 hcpt hcont y.1 y.2 k
  let step (k : Fin N) (y : K) : K :=
    ⟨Classical.choose (hs k y), (Classical.choose_spec (hs k y)).1⟩
  let seq : ℕ → K := fun r => Nat.rec (⟨x0, show f x0 ≤ f x0 from le_rfl⟩ : K) (fun r y => step (s r) y) r
  refine ⟨fun r => (seq r).1, rfl, hx0, ?_⟩
  intro r
  exact (Classical.choose_spec (hs (s r) (seq r))).2

theorem run_bounded {f : X n → EReal} (x0 : X n)
    (hcpt : IsCompact (levelSet f x0)) {s : ℕ → Fin N} {x : ℕ → X n}
    (h0 : x 0 = x0) (hr : IsBCDRun f s x) : Bornology.IsBounded (range x) :=
  hcpt.isBounded.subset (by rintro _ ⟨r, rfl⟩; exact run_mem hr x0 h0 r)

theorem run_values_tendsto (f : X n → EReal) (hbot : ∀ z, f z ≠ ⊥)
    (x0 : X n) (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y)
    {s : ℕ → Fin N} {x : ℕ → X n} (h0 : x 0 = x0) (hr : IsBCDRun f s x) :
    ∃ ell : EReal, ell ≠ ⊥ ∧ ell ≠ ⊤ ∧ ell ≤ f x0 ∧
      Tendsto (fun r => f (x r)) atTop (𝓝 ell) := by
  obtain ⟨z, hz, hm⟩ := hcpt.exists_isMinOn ⟨x0, show f x0 ≤ f x0 from le_rfl⟩
    (fun y hy => (hcont y hy).continuousWithinAt)
  let ell : EReal := ⨅ r, f (x r)
  have hl : f z ≤ ell := le_iInf fun r => hm (run_mem hr x0 h0 r)
  have hu : ell ≤ f x0 := by
    simpa only [h0] using (iInf_le (fun r => f (x r)) 0)
  refine ⟨ell, ?_, ?_, hu, tendsto_atTop_iInf (run_descent hr)⟩
  · intro he
    rw [he] at hl
    exact hbot z (le_bot_iff.mp hl)
  · intro he
    rw [he] at hu
    exact hx0 (top_le_iff.mp hu)

end TsengBCDProof
end
-- END RunBasics

-- BEGIN Directional
noncomputable section
namespace TsengBCDProof
open TsengBCD.Stationary Filter Topology Set
variable {N : ℕ} {n : Fin N → ℕ}

theorem add_single_eq_update (z : X n) (k : Fin N)
    (a : EuclideanSpace ℝ (Fin (n k))) :
    z + Pi.single k a = Function.update z k (z k + a) := by
  ext j
  by_cases hj : j = k
  · subst j; simp
  · simp [hj]

theorem blockMin_directional {f : X n → EReal} {z : X n} {k : Fin N}
    (htop : f z ≠ ⊤) (hbot : f z ≠ ⊥) (hm : BlockMin f z k)
    (d : EuclideanSpace ℝ (Fin (n k))) : 0 ≤ dirDeriv f z (Pi.single k d) := by
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  apply EReal.mul_nonneg
  · apply (EReal.sub_nonneg (Or.inr htop) (Or.inr hbot)).2
    have he : t • (Pi.single k d : X n) = Pi.single k (t • d) := by
      ext j
      by_cases hj : j = k
      · subst j; simp
      · simp [hj]
    rw [he, add_single_eq_update]
    exact hm _
  · exact_mod_cast (inv_nonneg.mpr ht'.le)

theorem dirDeriv_zero {f : X n → EReal} {z : X n}
    (htop : f z ≠ ⊤) (hbot : f z ≠ ⊥) : dirDeriv f z 0 = 0 := by
  simp [dirDeriv, EReal.sub_self htop hbot]

theorem stationary_of_blocks {f : X n → EReal} {z : X n}
    (hbot : f z ≠ ⊥) (hr : IsRegularAt f z) (hm : ∀ k, BlockMin f z k) :
    IsStationary f z := by
  refine ⟨hr.1, fun d => hr.2 d ?_⟩
  intro k
  exact blockMin_directional hr.1 hbot (hm k) (d k)

theorem coordMin_of_blocks {f : X n → EReal} {z : X n}
    (htop : f z ≠ ⊤) (hm : ∀ k, BlockMin f z k) : IsCoordMin f z := by
  refine ⟨htop, ?_⟩
  intro k d
  rw [add_single_eq_update]
  exact hm k _

theorem blocks_of_coordMin {f : X n → EReal} {z : X n}
    (hm : IsCoordMin f z) : ∀ k, BlockMin f z k := by
  intro k a
  have h := hm.2 k (a - z k)
  rw [add_single_eq_update] at h
  simpa only [add_sub_cancel] using h

theorem propagate_block {f : X n → EReal} {u v : X n} {a b : Fin N}
    (hbot : f u ≠ ⊥) (hr : IsRegularAt f u)
    (hp : PseudoconvexIn f {b, a}) (heq : f u = f v)
    (hagree : ∀ k, k ≠ b → v k = u k)
    (hma : BlockMin f u a) (hmb : BlockMin f u b) (hvb : BlockMin f v b) :
    BlockMin f v a := by
  classical
  by_cases hab : a = b
  · simpa only [hab] using hvb
  intro w
  let d : X n := v - u + Pi.single a (w - v a)
  have hd0 (k : Fin N) (hkb : k ≠ b) (hka : k ≠ a) : d k = 0 := by
    simp [d, hka, hagree k hkb]
  have hd : ∀ k, 0 ≤ dirDeriv f u (Pi.single k (d k)) := by
    intro k
    by_cases hka : k = a
    · subst k; exact blockMin_directional hr.1 hbot hma _
    by_cases hkb : k = b
    · subst k; exact blockMin_directional hr.1 hbot hmb _
    rw [hd0 k hkb hka]
    simpa only [Pi.single_zero, dirDeriv_zero hr.1 hbot] using (le_refl (0 : EReal))
  have hsupport : ∀ k, k ∉ ({b, a} : Set (Fin N)) → d k = 0 := by
    intro k hk
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hk
    exact hd0 k hk.1 hk.2
  have he : u + d = Function.update v a w := by
    ext k
    by_cases hk : k = a
    · subst k; simp [d]
    · simp [d, hk]
  have hh := hp u d hsupport hr.1 (hr.2 d hd)
  rw [he, heq] at hh
  exact hh

end TsengBCDProof
end
-- END Directional

-- BEGIN WindowExtraction
open Filter Topology Set

namespace TsengBCDProof
open TsengBCD.Stationary

variable {N : ℕ} {n : Fin N → ℕ}

/-- Extract actual simultaneous state and schedule limits. No window or minimum
relations are assumed: they follow from the supplied native run. -/
theorem extract_window (f : X n → EReal) (x0 : X n)
    (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y)
    (s : ℕ → Fin N) (x : ℕ → X n) (hrun : IsBCDRun f s x)
    (hmem : ∀ k, x k ∈ levelSet f x0) (ell : EReal)
    (hlim : Tendsto (fun k => f (x k)) atTop (𝓝 ell))
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (T : ℕ)
    (c : Fin (T + 1)) (target : X n)
    (hcenter : Tendsto (fun k => x (r k + c.val)) atTop (𝓝 target)) :
    ∃ W : Window f (levelSet f x0) T, W.z c = target ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ j : Fin T, ∀ᶠ k in atTop, s (r (φ k) + j.val) = W.label j := by
  classical
  let K := levelSet f x0
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcpt
  let u : ℕ → ((Fin (T + 1) → K) × (Fin T → Fin N)) := fun k =>
    (fun j => ⟨x (r k + j.val), hmem _⟩, fun j => s (r k + j.val))
  obtain ⟨a, φ, hφ, hu⟩ := CompactSpace.tendsto_subseq u
  let z : Fin (T + 1) → X n := fun j => (a.1 j).val
  let label : Fin T → Fin N := a.2
  have hz (j : Fin (T + 1)) :
      Tendsto (fun k => x (r (φ k) + j.val)) atTop (𝓝 (z j)) := by
    exact ((continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst)).tendsto a).comp hu
  have hl (j : Fin T) : ∀ᶠ k in atTop, s (r (φ k) + j.val) = label j := by
    have ht : Tendsto (fun k => s (r (φ k) + j.val)) atTop (𝓝 (label j)) :=
      (((continuous_apply j).comp continuous_snd).tendsto a).comp hu
    exact ht.eventually ((isOpen_discrete {label j}).mem_nhds rfl)
  have hv (j : Fin (T + 1)) : f (z j) = ell := by
    have hi : Tendsto (fun k => r (φ k) + j.val) atTop atTop :=
      tendsto_atTop_mono (fun k => Nat.le_add_right _ _) (hr.comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique ((hcont _ (a.1 j).property).tendsto.comp (hz j)) (hlim.comp hi)
  have hagree (j : Fin T) (k : Fin N) (hk : k ≠ label j) :
      z j.succ k = z j.castSucc k := by
    have he : ∀ᶠ q in atTop,
        x (r (φ q) + j.succ.val) k = x (r (φ q) + j.castSucc.val) k := by
      filter_upwards [hl j] with q hq
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using
        (hrun.2 (r (φ q) + j.val)).1 k (by simpa only [hq] using hk)
    exact tendsto_nhds_unique ((hz j.succ).apply_nhds k)
      (((hz j.castSucc).apply_nhds k).congr' (he.mono fun _ h => h.symm))
  have hmin (j : Fin T) : BlockMin f (z j.castSucc) (label j) := by
    intro v
    rw [hv]
    by_contra hn
    have hlt : f (Function.update (z j.castSucc) (label j) v) < ell := lt_of_not_ge hn
    have hw : Function.update (z j.castSucc) (label j) v ∈ levelSet f x0 := by
      change f (Function.update (z j.castSucc) (label j) v) ≤ f x0
      calc
        _ ≤ ell := hlt.le
        _ = f (z j.castSucc) := (hv _).symm
        _ ≤ f x0 := (a.1 j.castSucc).property
    have hright := (hcont _ hw).tendsto.comp ((hz j.castSucc).update (label j) tendsto_const_nhds)
    have hleft := (hcont _ (a.1 j.succ).property).tendsto.comp (hz j.succ)
    have he : ∀ᶠ q in atTop, f (x (r (φ q) + j.succ.val)) ≤
        f (Function.update (x (r (φ q) + j.castSucc.val)) (label j) v) := by
      filter_upwards [hl j] with q hq
      have hm := (hrun.2 (r (φ q) + j.val)).2
      rw [hq] at hm
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using hm v
    have hle := le_of_tendsto_of_tendsto hleft hright he
    rw [hv] at hle
    exact (not_le_of_gt hlt) hle
  have hminr (j : Fin T) : BlockMin f (z j.succ) (label j) := by
    intro v
    have he : Function.update (z j.succ) (label j) v =
        Function.update (z j.castSucc) (label j) v := by
      ext k
      by_cases hk : k = label j
      · subst k
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hk, hagree j k hk]
    rw [he, hv j.succ, ← hv j.castSucc]
    exact hmin j v
  let W : Window f (levelSet f x0) T :=
    ⟨z, label, fun j => (a.1 j).property, fun i j => (hv i).trans (hv j).symm,
      hagree, hmin, hminr⟩
  refine ⟨W, ?_, φ, hφ, hl⟩
  exact tendsto_nhds_unique (hz c) (hcenter.comp hφ.tendsto_atTop)

end TsengBCDProof
-- END WindowExtraction

-- BEGIN WindowSpecializations
open Filter Topology Set

namespace TsengBCDProof
open TsengBCD.Stationary

variable {N : ℕ} {n : Fin N → ℕ}

/-- An actual backwards window ends at any cluster point and retains coverage
of every block from the native essentially cyclic schedule. -/
theorem backward_window (f : X n → EReal) (x0 : X n)
    (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y)
    (s : ℕ → Fin N) (x : ℕ → X n) (hrun : IsBCDRun f s x)
    (hmem : ∀ k, x k ∈ levelSet f x0) (ell : EReal)
    (hlim : Tendsto (fun k => f (x k)) atTop (𝓝 ell))
    (T : ℕ) (hcover : ∀ r k, ∃ j < T, s (r + j) = k)
    (target : X n) (htarget : MapClusterPt target atTop x) :
    ∃ W : Window f (levelSet f x0) T, W.z (Fin.last T) = target ∧
      ∀ k : Fin N, ∃ j : Fin T, W.label j = k := by
  obtain ⟨φ, hφ, hxφ⟩ := htarget.tendsto_subseq
  let r : ℕ → ℕ := fun k => φ (k + T) - T
  have hbase (k : ℕ) : T ≤ φ (k + T) := by
    have hi : k + T ≤ φ (k + T) := hφ.id_le (k + T)
    omega
  have hr : Tendsto r atTop atTop := by
    apply tendsto_atTop_mono (f := id) _ tendsto_id
    intro k
    dsimp [r]
    have hi : k + T ≤ φ (k + T) := hφ.id_le (k + T)
    omega
  have hcenter : Tendsto (fun k => x (r k + (Fin.last T).val)) atTop (𝓝 target) := by
    have he : (fun k => x (r k + (Fin.last T).val)) = fun k => x (φ (k + T)) := by
      funext k
      simp only [r, Fin.val_last, Nat.sub_add_cancel (hbase k)]
    rw [he]
    exact hxφ.comp (tendsto_add_atTop_nat T)
  obtain ⟨W, hW, ψ, _, hlabels⟩ :=
    extract_window f x0 hcpt hcont s x hrun hmem ell hlim r hr T (Fin.last T) target hcenter
  refine ⟨W, hW, ?_⟩
  intro k
  have he : ∀ᶠ q in atTop, ∀ j : Fin T, s (r (ψ q) + j.val) = W.label j :=
    Filter.eventually_all.mpr hlabels
  obtain ⟨q, hq⟩ := he.exists
  obtain ⟨j, hj, hs⟩ := hcover (r (ψ q)) k
  exact ⟨⟨j, hj⟩, (hq ⟨j, hj⟩).symm.trans hs⟩

/-- For a cyclic run, extract the actual N successive transitions and retain
exact labels 0,...,N−1, centered at the native subsequence offset N−1. -/
theorem cyclic_window [NeZero N] (f : X n → EReal) (x0 : X n)
    (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y)
    (s : ℕ → Fin N) (x : ℕ → X n) (hrun : IsBCDRun f s x)
    (hmem : ∀ k, x k ∈ levelSet f x0) (ell : EReal)
    (hlim : Tendsto (fun k => f (x k)) atTop (𝓝 ell)) (hcyclic : IsCyclic s)
    (target : X n)
    (htarget : MapClusterPt target atTop (fun k : ℕ => x (N * k + (N - 1)))) :
    ∃ W : Window f (levelSet f x0) N,
      W.z ⟨N - 1, by omega⟩ = target ∧ ∀ j : Fin N, W.label j = j := by
  obtain ⟨φ, hφ, hxφ⟩ := htarget.tendsto_subseq
  let r : ℕ → ℕ := fun k => N * φ k
  have hN : 0 < N := NeZero.pos N
  have hr : Tendsto r atTop atTop := by
    apply tendsto_atTop_mono (f := φ) _ hφ.tendsto_atTop
    intro k
    dsimp [r]
    nlinarith
  let c : Fin (N + 1) := ⟨N - 1, by omega⟩
  have hcenter : Tendsto (fun k => x (r k + c.val)) atTop (𝓝 target) := hxφ
  obtain ⟨W, hW, ψ, _, hlabels⟩ :=
    extract_window f x0 hcpt hcont s x hrun hmem ell hlim r hr N c target hcenter
  refine ⟨W, hW, ?_⟩
  intro j
  obtain ⟨q, hq⟩ := (hlabels j).exists
  apply Fin.ext
  rw [← hq, hcyclic]
  simp only [r, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]

end TsengBCDProof
-- END WindowSpecializations

-- BEGIN WindowConclusions
noncomputable section
namespace TsengBCDProof
open TsengBCD.Stationary Filter Topology Set
variable {N : ℕ} {n : Fin N → ℕ}

theorem window_prefix_min {f : X n → EReal} {K : Set (X n)} {T : ℕ}
    (W : Window f K T) (hbot : ∀ z, f z ≠ ⊥)
    (hreg : ∀ z ∈ K, IsRegularAt f z) :
    ∀ (p : ℕ) (hp : p ≤ T),
      (∀ i j : Fin T, i.val < p → j.val < p → PseudoconvexIn f {W.label i, W.label j}) →
      ∀ a : Fin N, (∃ j : Fin T, j.val < p ∧ W.label j = a) →
        BlockMin f (W.z ⟨p, by omega⟩) a := by
  intro p
  induction p with
  | zero => intro _ _ a ha; obtain ⟨j, hj, _⟩ := ha; omega
  | succ p ih =>
    intro hp hpair a ha
    let j : Fin T := ⟨p, by omega⟩
    by_cases he : a = W.label j
    · simpa [he, j] using W.min_right j
    obtain ⟨i, hi, hia⟩ := ha
    have hip : i.val < p := by
      have hne : i.val ≠ p := by
        intro hh
        have hij : i = j := Fin.ext hh
        exact he (hia.symm.trans (congrArg W.label hij))
      omega
    have hpre := ih (by omega) (fun u v hu hv => hpair u v (by omega) (by omega))
      a ⟨i, hip, hia⟩
    have hh := propagate_block (hbot _) (hreg _ (W.mem j.castSucc))
      (by simpa only [hia] using hpair j i (by simp [j]) hi)
      (W.value_eq j.castSucc j.succ) (W.agree j) hpre (W.min_left j) (W.min_right j)
    exact hh

theorem window_all_stationary {f : X n → EReal} {K : Set (X n)} {T : ℕ}
    (W : Window f K T) (hbot : ∀ z, f z ≠ ⊥)
    (hreg : ∀ z ∈ K, IsRegularAt f z)
    (hp : ∀ i k : Fin N, PseudoconvexIn f {k, i})
    (hcover : ∀ k, ∃ j, W.label j = k) : IsStationary f (W.z (Fin.last T)) := by
  apply stationary_of_blocks (hbot _) (hreg _ (W.mem _))
  intro k
  obtain ⟨j, hj⟩ := hcover k
  exact window_prefix_min W hbot hreg T le_rfl
    (fun i l _ _ => hp (W.label l) (W.label i)) k ⟨j, j.isLt, hj⟩

theorem cyclic_prefix_stationary [NeZero N] {f : X n → EReal} {K : Set (X n)}
    (W : Window f K N) (hbot : ∀ z, f z ≠ ⊥)
    (hreg : ∀ z ∈ K, IsRegularAt f z)
    (hlab : ∀ j, W.label j = j)
    (hp : ∀ i k : Fin N, i.val < N - 1 → k.val < N - 1 → PseudoconvexIn f {k, i}) :
    IsStationary f (W.z ⟨N - 1, by have := NeZero.pos N; omega⟩) := by
  have hN := NeZero.pos N
  apply stationary_of_blocks (hbot _) (hreg _ (W.mem _))
  intro k
  by_cases hk : k.val < N - 1
  · apply window_prefix_min W hbot hreg (N - 1) (by omega)
    · intro i j hi hj
      simpa only [hlab] using hp j i hj hi
    · exact ⟨k, hk, hlab k⟩
  · have he : k.val = N - 1 := by omega
    have h := W.min_left k
    have hj : k.castSucc = (⟨N - 1, by omega⟩ : Fin (N + 1)) := Fin.ext he
    rw [hj, hlab] at h
    exact h


theorem window_unique_step {f : X n → EReal} {K : Set (X n)} {T : ℕ}
    (W : Window f K T) (j : Fin T) (htop : f (W.z j.castSucc) ≠ ⊤)
    (hu : AtMostOneMinIn f (W.label j)) : W.z j.castSucc = W.z j.succ := by
  classical
  let u := W.z j.castSucc
  let v := W.z j.succ
  let k := W.label j
  have hev : Function.update u k (v k) = v := by
    funext l
    by_cases hl : l = k
    · subst l; simp
    · simp only [Function.update_of_ne hl]
      exact (W.agree j l hl).symm
  have heq : u k = v k := by
    apply hu u (u k) (v k)
    · simpa only [k, u, Function.update_eq_self] using htop
    · simpa only [k, u, Function.update_eq_self, BlockMin] using W.min_left j
    · intro c
      rw [hev]
      change f (W.z j.succ) ≤ _
      rw [← W.value_eq j.castSucc j.succ]
      exact W.min_left j c
  funext l
  by_cases hl : l = k
  · subst l; exact heq
  · exact (W.agree j l hl).symm

theorem cyclic_unique_coordMin [NeZero N] {f : X n → EReal} {K : Set (X n)}
    (W : Window f K N) (htop : ∀ z ∈ K, f z ≠ ⊤)
    (hlab : ∀ j, W.label j = j)
    (hu : ∀ k : Fin N, 1 ≤ k.val → k.val < N - 1 → AtMostOneMinIn f k) :
    IsCoordMin f (W.z ⟨N - 1, by have := NeZero.pos N; omega⟩) := by
  have hN := NeZero.pos N
  apply coordMin_of_blocks (htop _ (W.mem _))
  intro k
  by_cases hk : k.val = N - 1
  · have hj : k.castSucc = (⟨N - 1, by omega⟩ : Fin (N + 1)) := Fin.ext hk
    have hh := W.min_left k
    rw [hj, hlab] at hh
    exact hh
  have hklt : k.val < N - 1 := by omega
  have hN2 : 1 < N := by omega
  have hchain : ∀ (q : ℕ) (hq : q < N), 1 ≤ q →
      W.z ⟨q, by omega⟩ = W.z ⟨1, by omega⟩ := by
    intro q
    induction q with
    | zero => intro _ hh; omega
    | succ q ih =>
      intro hq hq1
      by_cases he : q = 0
      · subst q; rfl
      have hstep := window_unique_step W (⟨q, by omega⟩ : Fin N)
        (htop _ (W.mem _)) (by rw [hlab]; exact hu ⟨q, by omega⟩ (by change 1 ≤ q; omega) (by change q < N - 1; omega))
      exact hstep.symm.trans (ih (by omega) (by omega))
  have he : W.z k.succ = W.z (⟨N - 1, by omega⟩ : Fin (N + 1)) :=
    (hchain (k.val + 1) (by omega) (by omega)).trans
      (hchain (N - 1) (by omega) (by omega)).symm
  have hh := W.min_right k
  rw [he, hlab] at hh
  exact hh

end TsengBCDProof
end
-- END WindowConclusions

-- BEGIN NativeRoot
namespace TsengBCD.Stationary

open Filter Topology

theorem theorem_4_1 {N : ℕ} [NeZero N] {n : Fin N → ℕ} (f : X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (x0 : X n) (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y) :
    -- defined: for every index sequence a BCD run from x⁰ exists
    (∀ s : ℕ → Fin N, ∃ x : ℕ → X n, x 0 = x0 ∧ IsBCDRun f s x) ∧
    -- bounded
    (∀ (s : ℕ → Fin N) (x : ℕ → X n), IsEssCyclic s → x 0 = x0 → IsBCDRun f s x →
      Bornology.IsBounded (Set.range x)) ∧
    -- (a)
    ((∀ i k : Fin N, PseudoconvexIn f {k, i}) → (∀ y ∈ levelSet f x0, IsRegularAt f y) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsEssCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop x → IsStationary f z) ∧
    -- (b)
    ((∀ i k : Fin N, i.val < N - 1 → k.val < N - 1 → PseudoconvexIn f {k, i}) →
      (∀ y ∈ levelSet f x0, IsRegularAt f y) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop (fun m : ℕ => x (N * m + (N - 1))) → IsStationary f z) ∧
    -- (c)
    ((∀ k : Fin N, 1 ≤ k.val → k.val < N - 1 → AtMostOneMinIn f k) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop (fun m : ℕ => x (N * m + (N - 1))) →
          IsCoordMin f z ∧ (IsRegularAt f z → IsStationary f z)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact TsengBCDProof.exists_run f x0 hx0 hcpt hcont
  · intro s x _ h0 hr
    exact TsengBCDProof.run_bounded x0 hcpt h0 hr
  · intro hp hreg s x hs h0 hr z hz
    obtain ⟨ell, _, _, _, hlim⟩ :=
      TsengBCDProof.run_values_tendsto f hbot x0 hx0 hcpt hcont h0 hr
    obtain ⟨T, _, hcover⟩ := hs
    obtain ⟨W, hW, hlabels⟩ := TsengBCDProof.backward_window f x0 hcpt hcont s x hr
      (TsengBCDProof.run_mem hr x0 h0) ell hlim T hcover z hz
    rw [← hW]
    exact TsengBCDProof.window_all_stationary W hbot hreg hp hlabels
  · intro hp hreg s x hs h0 hr z hz
    obtain ⟨ell, _, _, _, hlim⟩ :=
      TsengBCDProof.run_values_tendsto f hbot x0 hx0 hcpt hcont h0 hr
    obtain ⟨W, hW, hlabels⟩ := TsengBCDProof.cyclic_window f x0 hcpt hcont s x hr
      (TsengBCDProof.run_mem hr x0 h0) ell hlim hs z hz
    rw [← hW]
    exact TsengBCDProof.cyclic_prefix_stationary W hbot hreg hlabels hp
  · intro hu s x hs h0 hr z hz
    obtain ⟨ell, _, _, _, hlim⟩ :=
      TsengBCDProof.run_values_tendsto f hbot x0 hx0 hcpt hcont h0 hr
    obtain ⟨W, hW, hlabels⟩ := TsengBCDProof.cyclic_window f x0 hcpt hcont s x hr
      (TsengBCDProof.run_mem hr x0 h0) ell hlim hs z hz
    have htop : ∀ y ∈ levelSet f x0, f y ≠ ⊤ := by
      intro y hy he
      change f y ≤ f x0 at hy
      rw [he] at hy
      exact hx0 (top_le_iff.mp hy)
    have hm : IsCoordMin f z := by
      rw [← hW]
      exact TsengBCDProof.cyclic_unique_coordMin W htop hlabels hu
    refine ⟨hm, fun hreg => ?_⟩
    exact TsengBCDProof.stationary_of_blocks (hbot z) hreg
      (TsengBCDProof.blocks_of_coordMin hm)

end TsengBCD.Stationary
-- END NativeRoot

open TsengBCD.Stationary Filter Topology

theorem solution {N : ℕ} [NeZero N] {n : Fin N → ℕ} (f : X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (x0 : X n) (hx0 : f x0 ≠ ⊤) (hcpt : IsCompact (levelSet f x0))
    (hcont : ∀ y ∈ levelSet f x0, ContinuousAt f y) :
    -- defined: for every index sequence a BCD run from x⁰ exists
    (∀ s : ℕ → Fin N, ∃ x : ℕ → X n, x 0 = x0 ∧ IsBCDRun f s x) ∧
    -- bounded
    (∀ (s : ℕ → Fin N) (x : ℕ → X n), IsEssCyclic s → x 0 = x0 → IsBCDRun f s x →
      Bornology.IsBounded (Set.range x)) ∧
    -- (a)
    ((∀ i k : Fin N, PseudoconvexIn f {k, i}) → (∀ y ∈ levelSet f x0, IsRegularAt f y) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsEssCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop x → IsStationary f z) ∧
    -- (b)
    ((∀ i k : Fin N, i.val < N - 1 → k.val < N - 1 → PseudoconvexIn f {k, i}) →
      (∀ y ∈ levelSet f x0, IsRegularAt f y) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop (fun m : ℕ => x (N * m + (N - 1))) → IsStationary f z) ∧
    -- (c)
    ((∀ k : Fin N, 1 ≤ k.val → k.val < N - 1 → AtMostOneMinIn f k) →
      ∀ (s : ℕ → Fin N) (x : ℕ → X n), IsCyclic s → x 0 = x0 → IsBCDRun f s x →
        ∀ z, MapClusterPt z atTop (fun m : ℕ => x (N * m + (N - 1))) →
          IsCoordMin f z ∧ (IsRegularAt f z → IsStationary f z)) :=
  TsengBCD.Stationary.theorem_4_1 f hbot x0 hx0 hcpt hcont
