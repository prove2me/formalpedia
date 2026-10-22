-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P19.swap_channel_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:31:50.413928+00:00
-- url     : https://prove2.me/submissions/980ebe5d-0ca8-47ce-861d-3e3addd07513

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Support21.P19
attribute [local instance] Classical.propDecidable Classical.decEq

lemma g67b_chan_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (V : Matrix κ ι ℂ) (h : Vᴴ * V = 1) : IsChannel (conjSuperop V) :=
  ⟨1, fun _ => V, by simp [IsKrausFamily, h], fun ρ => by simp [krausApply, conjSuperop]⟩

lemma g67b_chan_id {ι : Type*} [Fintype ι] [DecidableEq ι] : IsChannel (fun M : Matrix ι ι ℂ => M) :=
  ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

@[simp] lemma g67b_sj {a b : ℕ} (x : Fin a) (y : Fin b) : split (joinRegisters x y) = (x,y) :=
  finProdFinEquiv.symm_apply_apply (x,y)

@[simp] lemma g67b_jv {a b : ℕ} (x : Fin a) (y : Fin b) :
    ((joinRegisters x y : Fin (a*b)) : ℕ) = y + b * x := finProdFinEquiv_apply_val (x, y)

@[simp] lemma g67b_s1v {a b : ℕ} (k : Fin (a*b)) : ((split k).1 : ℕ) = k / b := by
  simp [split]

@[simp] lemma g67b_s2v {a b : ℕ} (k : Fin (a*b)) : ((split k).2 : ℕ) = k % b := by
  simp [split]

lemma g67b_seq_eq {D : Type} {L : Kind → Resource} {a b c d : ℕ} {v : Kind → ℕ}
    {F G : D → Superop (Fin a × Fin b) (Fin c × Fin d)} (h : Sequential L a b c d v F) (e : F = G) :
    Sequential L a b c d v G := e ▸ h

/-- reindexing superoperators -/
def g67b_Re {α β : Type*} (Φ : Superop α β) (f : β → α) : Prop := ∀ M i j, Φ M i j = M (f i) (f j)

def g67b_perm {α β : Type*} (f : β → α) : Matrix β α ℂ := fun i a => if a = f i then 1 else 0

lemma g67b_re_conj {α β : Type*} [Fintype α] [Fintype β] (f : β → α) : g67b_Re (conjSuperop (g67b_perm f)) f := by
  intro M i j
  simp [conjSuperop, g67b_perm, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma g67b_perm_iso {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (f : β ≃ α) :
    (g67b_perm f)ᴴ * g67b_perm f = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g67b_perm, Matrix.one_apply]
  rw [Fintype.sum_equiv f _ (fun x => if a = x ∧ b = x then (1:ℂ) else 0) (fun x => by
    by_cases h1 : a = f x <;> by_cases h2 : b = f x <;> simp [h1, h2])]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, if_false]; apply Finset.sum_eq_zero; intro x _; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

lemma g67b_re_extend (R : Resource) (ma mb : ℕ) (f : Fin R.ao × Fin R.bo → Fin R.ai × Fin R.bi)
    (h : g67b_Re R.map f) : g67b_Re (extend R ma mb) (fun i =>
      (joinRegisters (f ((split i.1).1, (split i.2).1)).1 (split i.1).2,
       joinRegisters (f ((split i.1).1, (split i.2).1)).2 (split i.2).2)) := by
  intro M i j; exact h _ _ _

lemma g67b_re_comp {α β γ : Type*} (F : Superop α β) (G : Superop β γ) (f : β → α) (g : γ → β)
    (hF : g67b_Re F f) (hG : g67b_Re G g) : g67b_Re (G ∘ F) (f ∘ g) := by
  intro M i j; exact (hG _ _ _).trans (hF _ _ _)

lemma g67b_re_local {a b c d : ℕ} (A : Superop (Fin a) (Fin c)) (B : Superop (Fin b) (Fin d))
    (f : Fin c → Fin a) (g : Fin d → Fin b) (hA : g67b_Re A f) (hB : g67b_Re B g) :
    g67b_Re (localMap A B) (fun i => (f i.1, g i.2)) := by
  intro M i j; exact (hB _ _ _).trans (hA _ _ _)

lemma g67b_re_tensor (R S : Resource) (f : Fin R.ao × Fin R.bo → Fin R.ai × Fin R.bi)
    (g : Fin S.ao × Fin S.bo → Fin S.ai × Fin S.bi) (hR : g67b_Re R.map f) (hS : g67b_Re S.map g) :
    g67b_Re (tensorResources R S).map (fun i =>
      (joinRegisters (f ((split i.1).1, (split i.2).1)).1 (g ((split i.1).2, (split i.2).2)).1,
       joinRegisters (f ((split i.1).1, (split i.2).1)).2 (g ((split i.1).2, (split i.2).2)).2)) := by
  intro M i j
  change Matrix (Fin (R.ai*S.ai) × Fin (R.bi*S.bi)) (Fin (R.ai*S.ai) × Fin (R.bi*S.bi)) ℂ at M
  change Fin (R.ao*S.ao) × Fin (R.bo*S.bo) at i j
  simp only [tensorResources]
  unfold g67b_Re at hR hS
  simp only [hR, hS, Matrix.single_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma g67b_re_reverse (R : Resource) (f : Fin R.ao × Fin R.bo → Fin R.ai × Fin R.bi) (h : g67b_Re R.map f) :
    g67b_Re (reverse R).map (fun i => ((f (i.2, i.1)).2, (f (i.2, i.1)).1)) := by
  intro M i j; exact h _ _ _

lemma g67b_re_qubit : g67b_Re (qubitChannel 2).map (fun i : Fin 1 × Fin 2 => (i.2, (0 : Fin 1))) := fun _ _ _ => rfl

lemma g67b_re_idle (a b : ℕ) : g67b_Re (idle a b).map id := fun _ _ _ => rfl

lemma g67b_swap_mat : (QAlgorithms.swapGate.submatrix
      (fun i : Fin 2 × Fin 2 => (decide (i.1 = 1), decide (i.2 = 1)))
      (fun i : Fin 2 × Fin 2 => (decide (i.1 = 1), decide (i.2 = 1)))) = g67b_perm (fun p : Fin 2 × Fin 2 => (p.2, p.1)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [swapGate, g67b_perm]

lemma g67b_re_swap : g67b_Re swapResource.map (fun p : Fin 2 × Fin 2 => (p.2, p.1)) := by
  have : swapResource.map = conjSuperop (g67b_perm (fun p : Fin 2 × Fin 2 => (p.2, p.1))) := by
    simp only [swapResource]; rw [g67b_swap_mat]
  rw [this]; exact g67b_re_conj _

lemma g67b_re_eq {α β : Type*} (F G : Superop α β) (f g : β → α) (hF : g67b_Re F f) (hG : g67b_Re G g)
    (h : ∀ i, f i = g i) : F = G := by
  funext M i j; rw [hF, hG, h, h]

lemma g67b_swapA : Exact swapResource (budget 1 0 0 0 0 0 0 0)
    (tensorResources (tensorResources (qubitChannel 2) (reverse (qubitChannel 2))) (resourceTensorCopies (entangled 2) 0)) := by
  have s := Sequential.callStep (L := library swapResource) (D := Unit) Kind.main 1 1
  have hL := g67b_re_extend (library swapResource Kind.main) 1 1 _ g67b_re_swap
  have hR := g67b_re_tensor _ _ _ _ (g67b_re_tensor _ _ _ _ g67b_re_qubit (g67b_re_reverse _ _ g67b_re_qubit))
    (g67b_re_idle 1 1)
  refine ⟨oneCall Kind.main, ?_, g67b_seq_eq s (funext fun _ => g67b_re_eq _ _ _ _ hL hR (fun i => ?_))⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · rcases i with ⟨a, b⟩
    change Fin (2*1) at a b
    fin_cases a <;> fin_cases b <;> rfl

def g67b_sw : Fin (2*2) ≃ Fin (2*2) := finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

lemma g67b_re_id {α : Type*} : g67b_Re (fun M : Matrix α α ℂ => M) id := fun _ _ _ => rfl

lemma g67b_swapB : Exact (idle 1 1) (budget 0 0 1 1 0 0 0 0)
    (tensorResources swapResource (resourceTensorCopies (entangled 2) 0)) := by
  have s1 := Sequential.callStep (L := library (idle 1 1)) (D := Unit) Kind.qubitF 1 2
  have s2 := Sequential.localStep (L := library (idle 1 1)) (D := Unit) (fun _ => fun M : Matrix (Fin (1*1)) (Fin (1*1)) ℂ => M)
    (conjSuperop (g67b_perm g67b_sw)) (fun _ => g67b_chan_id) (g67b_chan_conj _ (g67b_perm_iso g67b_sw))
  have s3 := Sequential.callStep (L := library (idle 1 1)) (D := Unit) Kind.qubitB 1 2
  have s := Sequential.compose (Sequential.compose s1 s2) s3
  have h1 := g67b_re_extend (library (idle 1 1) Kind.qubitF) 1 2 _ g67b_re_qubit
  have h2 := g67b_re_local _ _ _ _ (g67b_re_id (α := Fin (1*1))) (g67b_re_conj g67b_sw)
  have h3 := g67b_re_extend (library (idle 1 1) Kind.qubitB) 1 2 _ (g67b_re_reverse _ _ g67b_re_qubit)
  have hL := g67b_re_comp _ _ _ _ (g67b_re_comp _ _ _ _ h1 h2) h3
  have hR := g67b_re_tensor _ _ _ _ g67b_re_swap (g67b_re_idle 1 1)
  refine ⟨_, ?_, g67b_seq_eq s (funext fun _ => g67b_re_eq _ _ _ _ hL hR (fun i => ?_))⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · rcases i with ⟨a, b⟩
    change Fin 2 at a b
    fin_cases a <;> fin_cases b <;> rfl

theorem g67b_swap_channel_equivalence :
    ∃ k : ℕ,
      Exact swapResource (budget 1 k 0 0 0 0 0 0)
        (tensorResources (tensorResources (qubitChannel 2) (reverse (qubitChannel 2))) (resourceTensorCopies (entangled 2) k)) ∧
      Exact (idle 1 1) (budget 0 k 1 1 0 0 0 0) (tensorResources swapResource (resourceTensorCopies (entangled 2) k)) :=
  ⟨0, g67b_swapA, g67b_swapB⟩

/-- PDF p.2: catalytic SWAP versus two opposite quantum channels, on arbitrary quantum inputs. -/
theorem solution :
    ∃ k : ℕ,
      Exact swapResource (budget 1 k 0 0 0 0 0 0)
        (tensorResources (tensorResources (qubitChannel 2) (reverse (qubitChannel 2))) (resourceTensorCopies (entangled 2) k)) ∧
      Exact (idle 1 1) (budget 0 k 1 1 0 0 0 0) (tensorResources swapResource (resourceTensorCopies (entangled 2) k)) :=
  g67b_swap_channel_equivalence
